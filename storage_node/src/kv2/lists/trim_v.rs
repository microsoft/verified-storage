#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

impl<L> ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn entry(self) -> ListTableDurableEntry
    {
        match self {
            ListTableEntryView::<L>::Durable{ entry } => entry,
            ListTableEntryView::<L>::Modified{ entry, .. } => entry,
        }
    }

    pub(super) open spec fn length(self) -> usize
    {
        self.entry().length
    }
}

impl<L> ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn trim(self, list_addr: u64, trim_length: int) -> Self
        recommends
            self.list_info.contains_key(list_addr),
            0 < trim_length < self.list_info[list_addr].len(),
    {
        let new_head = self.list_info[list_addr][trim_length];
        let new_addrs = self.list_info[list_addr].skip(trim_length);
        let new_elements = self.list_elements[list_addr].skip(trim_length);
        let new_row_info = Map::<u64, ListRowRecoveryInfo<L>>::new(
            |row_addr: u64| {
                &&& self.row_info.contains_key(row_addr)
                &&& self.row_info[row_addr].head == list_addr ==> self.row_info[row_addr].pos >= trim_length
            },
            |row_addr: u64|
            {
                let info = self.row_info[row_addr];
                if info.head == list_addr {
                    ListRowRecoveryInfo::<L>{ head: new_head, pos: info.pos - trim_length, ..info }
                }
                else {
                    info
                }
            }
        );
        Self{
            row_info: new_row_info,
            list_info: self.list_info.remove(list_addr).insert(new_head, new_addrs),
            list_elements: self.list_elements.remove(list_addr).insert(new_head, new_elements),
        }
    }
}

impl<L> ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn trim(self, new_head: u64, trim_length: int, num_modifications: nat) -> Self
        recommends
            match self {
                ListTableEntryView::Durable{ entry } => 0 < trim_length < entry.length,
                ListTableEntryView::Modified{ entry, .. } => 0 < trim_length < entry.length,
            },
    {
        match self {
            ListTableEntryView::Durable{ entry } =>
                ListTableEntryView::Modified{
                    which_modification: num_modifications,
                    durable_head: entry.head,
                    entry: ListTableDurableEntry{
                        head: new_head,
                        length: (entry.length - trim_length) as usize,
                        ..entry
                    },
                    addrs: Seq::<u64>::empty(),
                    elements: Seq::<L>::empty(),
                },
            ListTableEntryView::Modified{ which_modification, durable_head, entry, addrs, elements } => {
                let new_length = entry.length - trim_length;
                ListTableEntryView::Modified{
                    which_modification,
                    durable_head: if new_length > addrs.len() { durable_head } else { 0 },
                    entry: ListTableDurableEntry{
                        head: new_head,
                        length: new_length as usize,
                        ..entry
                    },
                    addrs: if new_length <= addrs.len() { addrs.skip(addrs.len() - new_length) } else { addrs },
                    elements: if new_length <= elements.len() { elements.skip(elements.len() - new_length) }
                              else { elements },
                }
            },
        }
    }
}

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn trim(self, list_addr: u64, trim_length: int) -> Self
        recommends
            self.m.contains_key(list_addr),
            0 < trim_length < self.tentative_mapping.list_info[list_addr].len(),
    {
        let new_head = self.tentative_mapping.list_info[list_addr][trim_length];
        let new_row_info = Map::<u64, ListRowDisposition>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64|
                if {
                    &&& self.tentative_mapping.row_info.contains_key(row_addr)
                    &&& self.tentative_mapping.row_info[row_addr].head == list_addr
                    &&& self.tentative_mapping.row_info[row_addr].pos < trim_length
                } {
                    self.row_info[row_addr].add_to_pending_deallocations(
                        self.pending_deallocations.len() + self.tentative_mapping.row_info[row_addr].pos as nat
                    )
                } else {
                    self.row_info[row_addr]
                },
        );
        let new_deletes =
            if let ListTableEntryView::Durable{ entry } = self.m[list_addr] {
                self.deletes.push(entry)
            }
            else {
                self.deletes
            };
        let new_deletes_inverse =
            if self.m[list_addr] is Durable {
                self.deletes_inverse.insert(list_addr, self.deletes.len())
            }
            else {
                self.deletes_inverse
            };
        let new_entry = self.m[list_addr].trim(new_head, trim_length, self.modifications.len());
        let new_modifications =
            match self.m[list_addr] {
                ListTableEntryView::Durable{ .. } =>
                    self.modifications.push(Some(new_head)),
                ListTableEntryView::Modified{ which_modification, .. } =>
                    self.modifications.update(which_modification as int, Some(new_head)),
            };
        Self{
            tentative_list_addrs: self.tentative_list_addrs.remove(list_addr).insert(new_head),
            tentative_mapping: self.tentative_mapping.trim(list_addr, trim_length),
            row_info: new_row_info,
            m: self.m.remove(list_addr).insert(new_head, new_entry),
            deletes_inverse: new_deletes_inverse,
            deletes: new_deletes,
            modifications: new_modifications,
            pending_deallocations:
                self.pending_deallocations + self.tentative_mapping.list_info[list_addr].take(trim_length),
            ..self
        }
    }

    pub(super) proof fn lemma_trim_works(
        self,
        list_addr: u64,
        trim_length: int,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.valid(sm),
            0 < sm.start(),
            self.durable_mapping.internally_consistent(sm),
            self.tentative_mapping.internally_consistent(sm),
            self.m.contains_key(list_addr),
            0 < trim_length < self.m[list_addr].length(),
        ensures
            self.trim(list_addr, trim_length).valid(sm),
            ({
                let new_head = self.tentative_mapping.list_info[list_addr][trim_length];
                self.trim(list_addr, trim_length).tentative_mapping.as_snapshot() ==
                    self.tentative_mapping.as_snapshot().trim(list_addr, new_head, trim_length)
            }),
    {
        let new_head = self.tentative_mapping.list_info[list_addr][trim_length];
        let new_self = self.trim(list_addr, trim_length);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();

        assert(new_head > 0) by {
            broadcast use group_validate_row_addr;
        }

        assert(new_snapshot =~= old_snapshot.trim(list_addr, new_head, trim_length));
        assert(self.trim(list_addr, trim_length).tentative_mapping.as_snapshot() =~=
               self.tentative_mapping.as_snapshot().trim(list_addr, new_head, trim_length));

        if let ListTableEntryView::Modified{ durable_head, entry, addrs, elements, .. } = new_self.m[new_head] {
            let tentative_addrs = new_self.tentative_mapping.list_info[new_head];
            let tentative_elements = new_self.tentative_mapping.list_elements[new_head];
            if addrs.len() == entry.length {
                assert(tentative_addrs =~= addrs);
                assert(tentative_elements =~= elements);
            }
            else {
                let durable_addrs = new_self.durable_mapping.list_info[durable_head];
                let durable_elements = new_self.durable_mapping.list_elements[durable_head];
                assert(new_self.durable_mapping.list_info.contains_key(durable_head));
                assert(tentative_addrs =~=
                       durable_addrs.skip(durable_addrs.len() - (entry.length - addrs.len())) + addrs);
                assert(tentative_elements =~=
                       durable_elements.skip(durable_elements.len() - (entry.length - elements.len())) +
                       elements);
            }
        }
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn trim(
        &mut self,
        row_addr: u64,
        trim_length: usize,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
            0 < trim_length,
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[row_addr];
                    &&& {
                           ||| new_row_addr == 0
                           ||| new_row_addr == row_addr
                           ||| !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    }
                    &&& trim_length <= old_list.len()
                    &&& new_row_addr == 0 ==> old_list.skip(trim_length as int) == Seq::<L>::empty()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().trim(row_addr, new_row_addr, trim_length as int)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    &&& self@ == old(self)@
                    &&& trim_length > upper_bound
                    &&& upper_bound == old(self)@.tentative.unwrap().m[row_addr].len()
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            }
    {
        proof {
            broadcast use group_hash_axioms;
        }
        /*

        let result = match self.m.get(&list_addr) {
            None => {
                assert(false);
                Err(KvError::InternalError)
            },
            Some(ListTableEntry::<L>::Durable{ ref entry }) =>
                self.get_addresses_to_trim_case_durable(list_addr, trim_length, entry, journal),
            Some(ListTableEntry::<L>::Modified{ ref durable_head, ref entry, ref elements, .. }) =>
                self.get_addresses_to_trim_case_modified(list_addr, trim_length, Ghost(durable_head@), entry,
                                                         elements, journal),
        };
        */

        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

