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

    pub(super) open spec fn valid(self) -> bool
    {
        match self {
            ListTableEntryView::Durable{ entry } => true,
            ListTableEntryView::Modified{ entry, addrs, elements, .. } => {
                &&& entry.length >= addrs.len()
                &&& addrs.len() == elements.len()
            },
        }
    }

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

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn entry(self) -> ListTableDurableEntry
    {
        match self {
            ListTableEntry::Durable{ entry } => entry,
            ListTableEntry::Modified{ entry, .. } => entry,
        }
    }

    pub(super) open spec fn length(self) -> usize
    {
        self.entry().length
    }

    exec fn trim(self, new_head: u64, trim_length: usize, num_modifications: usize)
                 -> (result: (ListTableDurableEntry, Self))
        requires
            self@.valid(),
            0 < trim_length < self.length(),
        ensures
            ({
                let (durable_entry, new_self) = result;
                &&& new_self@ == self@.trim(new_head, trim_length as int, num_modifications as nat)
                &&& durable_entry == self@.entry()
            }),
    {
        match self {
            ListTableEntry::Durable{ entry } =>
            {
                (entry, ListTableEntry::Modified{
                    which_modification: num_modifications,
                    durable_head: Ghost(entry.head),
                    entry: ListTableDurableEntry{
                        head: new_head,
                        length: (entry.length - trim_length) as usize,
                        ..entry
                    },
                    addrs: Vec::<u64>::new(),
                    elements: Vec::<L>::new(),
                })
            },
            ListTableEntry::Modified{ which_modification, durable_head, entry, mut addrs, mut elements } =>
            {
                let new_length = entry.length - trim_length;
                let addrs_len = if new_length < addrs.len() { addrs.len() - new_length } else { 0 };
                assert(addrs@.skip(0) =~= addrs@);
                assert(elements@.skip(0) =~= elements@);
                (entry, ListTableEntry::Modified{
                    which_modification: which_modification,
                    durable_head: if new_length > addrs.len() { durable_head } else { Ghost(0) },
                    entry: ListTableDurableEntry{
                        head: new_head,
                        length: new_length as usize,
                        ..entry
                    },
                    addrs: if new_length < addrs.len() { addrs.split_off(addrs_len) } else { addrs },
                    elements: if new_length < elements.len() { elements.split_off(addrs_len) } else { elements },
                })
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

enum TrimAction
{
    Delete,
    Modify{ pending_deallocations: Vec<u64>, new_head: u64 },
    Advance{ pending_deallocations: Vec<u64>, new_head: u64 },
    Drain{ pending_deallocations: Vec<u64> },
}

impl TrimAction
{
    spec fn applicable<L>(self, iv: ListTableInternalView<L>, list_addr: u64, trim_length: int) -> bool
        where
            L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
        recommends
            iv.tentative_mapping.list_info.contains_key(list_addr),
    {
        match self {
            TrimAction::Delete => iv.tentative_mapping.list_info[list_addr].len() == trim_length,
            TrimAction::Modify{ pending_deallocations, new_head } => {
                &&& 0 < trim_length < iv.tentative_mapping.list_info[list_addr].len()
                &&& iv.m.contains_key(list_addr)
                &&& iv.m[list_addr] is Durable
                &&& pending_deallocations@ == iv.tentative_mapping.list_info[list_addr].take(trim_length)
                    &&& new_head == iv.tentative_mapping.list_info[list_addr][trim_length]
            },
            TrimAction::Advance{ pending_deallocations, new_head } => {
                &&& 0 < trim_length < iv.tentative_mapping.list_info[list_addr].len()
                &&& iv.m.contains_key(list_addr)
                &&& new_head == iv.tentative_mapping.list_info[list_addr][trim_length]
                &&& pending_deallocations@ == iv.tentative_mapping.list_info[list_addr].take(trim_length)
                &&& match iv.m[list_addr] {
                    ListTableEntryView::Modified{ entry, addrs, .. } => entry.length - trim_length > addrs.len(),
                    _ => false,
                }
            },
            TrimAction::Drain{ pending_deallocations } => {
                &&& 0 < trim_length < iv.tentative_mapping.list_info[list_addr].len()
                &&& iv.m.contains_key(list_addr)
                &&& match iv.m[list_addr] {
                       ListTableEntryView::Modified{ entry, addrs, .. } => {
                           &&& entry.length - trim_length <= addrs.len()
                           &&& pending_deallocations@ ==
                                  iv.tentative_mapping.list_info[list_addr].take(entry.length - addrs.len())
                       },
                       _ => false,
                   }
            },
        }
    }

    spec fn apply<L>(self, iv: ListTableInternalView<L>, list_addr: u64, trim_length: int) -> ListTableInternalView<L>
        where
            L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
        recommends
            iv.tentative_mapping.list_info.contains_key(list_addr),
    {
        let new_iv = iv.trim(list_addr, trim_length);
        match self {
            TrimAction::Delete => iv,
            TrimAction::Modify{ pending_deallocations, new_head } => {
                let old_entry = iv.m[list_addr]->Durable_entry;
                let new_entry = iv.m[list_addr].trim(new_head, trim_length, iv.modifications.len());
                ListTableInternalView::<L>{
                    m: iv.m.remove(list_addr).insert(new_head, new_entry),
                    deletes: iv.deletes.push(old_entry),
                    modifications: iv.modifications.push(Some(new_head)),
                    pending_deallocations: iv.pending_deallocations + pending_deallocations@,
                    ..new_iv
                }
            },
            TrimAction::Advance{ pending_deallocations, new_head } => {
                let which_modification = iv.m[list_addr]->Modified_which_modification;
                let new_entry = iv.m[list_addr].trim(new_head, trim_length, iv.modifications.len());
                ListTableInternalView::<L>{
                    m: iv.m.remove(list_addr).insert(new_head, new_entry),
                    modifications: iv.modifications.update(which_modification as int, Some(new_head)),
                    pending_deallocations: iv.pending_deallocations + pending_deallocations@,
                    ..new_iv
                }
            },
            TrimAction::Drain{ pending_deallocations } => {
                let which_modification = iv.m[list_addr]->Modified_which_modification;
                let old_entry = iv.m[list_addr]->Modified_entry;
                let addrs = iv.m[list_addr]->Modified_addrs;
                let num_addrs_to_drain = addrs.len() - (old_entry.length - trim_length);
                let new_head = addrs[num_addrs_to_drain];
                let new_entry = iv.m[list_addr].trim(new_head, trim_length, iv.modifications.len());
                ListTableInternalView::<L>{
                    m: iv.m.remove(list_addr).insert(new_head, new_entry),
                    modifications: iv.modifications.update(which_modification as int, Some(new_head)),
                    pending_deallocations: iv.pending_deallocations + pending_deallocations@ +
                                           iv.m[list_addr]->Modified_addrs.take(num_addrs_to_drain),
                    ..new_iv
                }
            },
        }
    }

    proof fn lemma_action_works<L>(
        self,
        iv: ListTableInternalView<L>,
        list_addr: u64,
        trim_length: int,
        sm: ListTableStaticMetadata,
    )
        where
            L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
        requires
            iv.tentative_mapping.list_info.contains_key(list_addr),
            iv.valid(sm),
            iv.durable_mapping.internally_consistent(sm),
            iv.tentative_mapping.internally_consistent(sm),
            self.applicable::<L>(iv, list_addr, trim_length),
            !(self is Delete),
        ensures
            self.apply(iv, list_addr, trim_length) == iv.trim(list_addr, trim_length),
    {
        assert(self.apply(iv, list_addr, trim_length) =~= iv.trim(list_addr, trim_length));
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn get_addresses_to_trim_case_durable(
        &self,
        list_addr: u64,
        trim_length: usize,
        entry: &ListTableDurableEntry,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<(Vec<u64>, u64), KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Durable,
            entry == self.m@[list_addr]->Durable_entry,
            trim_length < entry.length,
        ensures
            match result {
                Ok((addrs, new_head)) => {
                    &&& addrs@ == self.tentative_mapping@.list_info[list_addr].take(trim_length as int)
                    &&& new_head == self.tentative_mapping@.list_info[list_addr][trim_length as int]
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result = Vec::<u64>::new();
        let ghost addrs = self.durable_mapping@.list_info[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(addrs.take(0) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }
        
        for current_pos in 0..trim_length
            invariant
                trim_length < addrs.len(),
                current_addr == addrs[current_pos as int],
                current_addr != 0,
                result@ == addrs.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(list_addr),
                addrs == self.durable_mapping@.list_info[list_addr],
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
            decreases
                addrs.len() - result@.len(),
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(addrs.take(current_pos as int).push(current_addr) =~= addrs.take(current_pos + 1));
            result.push(current_addr);

            let next_addr = current_addr + self.sm.row_next_start;
            let next_crc_addr = next_addr + size_of::<u64>() as u64;
            current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                Some(n) => n,
                None => { return Err(KvError::CRCMismatch); },
            };
        }
        
        assert(self.tentative_mapping@.list_info[list_addr] == self.durable_mapping@.list_info[list_addr]);
        Ok((result, current_addr))
    }

    exec fn get_addresses_to_trim_case_advance(
        &self,
        list_addr: u64,
        trim_length: usize,
        Ghost(durable_head): Ghost<u64>,
        entry: &ListTableDurableEntry,
        addrs: &Vec<u64>,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<(Vec<u64>, u64), KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Modified,
            durable_head == self.m@[list_addr]->Modified_durable_head,
            entry == self.m@[list_addr]->Modified_entry,
            addrs == self.m@[list_addr]->Modified_addrs,
            trim_length < entry.length - addrs.len(),
        ensures
            match result {
                Ok((addrs, new_head)) => {
                    &&& addrs@ == self.tentative_mapping@.list_info[list_addr].take(trim_length as int)
                    &&& new_head == self.tentative_mapping@.list_info[list_addr][trim_length as int]
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result = Vec::<u64>::new();
        let ghost durable_addrs = self.durable_mapping@.list_info[durable_head];
        let ghost tentative_addrs = self.tentative_mapping@.list_info[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(tentative_addrs.take(0) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }
        
        for current_pos in 0..trim_length
            invariant
                trim_length < entry.length - addrs.len(),
                current_addr == tentative_addrs[current_pos as int],
                current_addr != 0,
                result@ == tentative_addrs.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(durable_head),
                self.tentative_mapping@.list_info.contains_key(list_addr),
                0 < durable_addrs.len(),
                addrs.len() < entry.length,
                entry.length - addrs.len() <= durable_addrs.len(),
                durable_addrs == self.durable_mapping@.list_info[durable_head],
                tentative_addrs == self.tentative_mapping@.list_info[list_addr],
                tentative_addrs == durable_addrs.skip(durable_addrs.len() - (entry.length - addrs.len())) + addrs@,
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(tentative_addrs.take(current_pos as int).push(current_addr) =~=
                   tentative_addrs.take(current_pos + 1));
            result.push(current_addr);

            let next_addr = current_addr + self.sm.row_next_start;
            let next_crc_addr = next_addr + size_of::<u64>() as u64;
            current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                Some(n) => n,
                None => { return Err(KvError::CRCMismatch); },
            };
        }
        
        Ok((result, current_addr))
    }

    exec fn get_addresses_to_trim_case_drain(
        &self,
        list_addr: u64,
        num_durable_addrs: usize,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<u64>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Modified,
            num_durable_addrs == self.m@[list_addr]->Modified_entry.length - self.m@[list_addr]->Modified_addrs.len(),
        ensures
            match result {
                Ok(addrs) => addrs@ == self.tentative_mapping@.list_info[list_addr].take(num_durable_addrs as int),
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut result = Vec::<u64>::new();
        let ghost tentative_addrs = self.tentative_mapping@.list_info[list_addr];

        if num_durable_addrs == 0 {
            assert(tentative_addrs.take(0) =~= Seq::<u64>::empty());
            return Ok(result);
        }

        let mut current_addr = list_addr;
        let ghost durable_head = self.m@[list_addr]->Modified_durable_head@;
        let ghost entry = self.m@[list_addr]->Modified_entry;
        let ghost addrs = self.m@[list_addr]->Modified_addrs;
        let ghost durable_addrs = self.durable_mapping@.list_info[durable_head];
        let pm = journal.get_pm_region_ref();

        assert(tentative_addrs.take(0) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        for current_pos in 0..num_durable_addrs
            invariant
                num_durable_addrs == entry.length - addrs.len(),
                current_pos < num_durable_addrs ==> current_addr == tentative_addrs[current_pos as int],
                current_pos < num_durable_addrs ==> current_addr != 0,
                result@ == tentative_addrs.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(durable_head),
                self.tentative_mapping@.list_info.contains_key(list_addr),
                0 < durable_addrs.len(),
                addrs.len() < entry.length,
                entry.length - addrs.len() <= durable_addrs.len(),
                durable_addrs == self.durable_mapping@.list_info[durable_head],
                tentative_addrs == self.tentative_mapping@.list_info[list_addr],
                tentative_addrs == durable_addrs.skip(durable_addrs.len() - (entry.length - addrs.len())) + addrs@,
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(tentative_addrs.take(current_pos as int).push(current_addr) =~=
                   tentative_addrs.take(current_pos + 1));
            result.push(current_addr);

            if current_pos < num_durable_addrs {
                let next_addr = current_addr + self.sm.row_next_start;
                let next_crc_addr = next_addr + size_of::<u64>() as u64;
                current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                    Some(n) => n,
                    None => { return Err(KvError::CRCMismatch); },
                };
            }
        }
        
        Ok(result)
    }

    #[inline]
    exec fn determine_action(
        &self,
        list_addr: u64,
        trim_length: usize,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<TrimAction, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative is Some,
            self@.tentative.unwrap().m.contains_key(list_addr),
            0 < trim_length,
        ensures
            match result {
                Ok(action) => action.applicable(self.internal_view(), list_addr, trim_length as int),
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    &&& upper_bound == self@.tentative.unwrap().m[list_addr].len()
                    &&& upper_bound < trim_length
                },
                _ => false,
            }
    {
        proof {
            self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            broadcast use group_hash_axioms;
        }

        match self.m.get(&list_addr) {
            None => {
                assert(false);
                Err(KvError::InternalError)
            },
            Some(ListTableEntry::<L>::Durable{ ref entry }) => {
                if entry.length < trim_length {
                    Err(KvError::IndexOutOfRange{ upper_bound: entry.length })
                }
                else if entry.length == trim_length {
                    Ok(TrimAction::Delete)
                }
                else {
                    match self.get_addresses_to_trim_case_durable(list_addr, trim_length, entry, journal) {
                        Ok((pending_deallocations, new_head)) =>
                            Ok(TrimAction::Modify{ pending_deallocations, new_head }),
                        Err(KvError::CRCMismatch) => Err(KvError::CRCMismatch),
                        _ => { assert(false); Err(KvError::InternalError) },
                    }
                }
            }
            Some(ListTableEntry::<L>::Modified{ ref durable_head, ref entry, ref addrs, .. }) => {
                if entry.length < trim_length {
                    Err(KvError::IndexOutOfRange{ upper_bound: entry.length })
                }
                else if entry.length == trim_length {
                    Ok(TrimAction::Delete)
                }
                else if trim_length < entry.length - addrs.len() {
                    match self.get_addresses_to_trim_case_advance(list_addr, trim_length, Ghost(durable_head@),
                                                                  entry, addrs, journal) {
                        Ok((pending_deallocations, new_head)) =>
                            Ok(TrimAction::Advance{ pending_deallocations, new_head }),
                        Err(KvError::CRCMismatch) => Err(KvError::CRCMismatch),
                        _ => { assert(false); Err(KvError::InternalError) },
                    }
                }
                else {
                    match self.get_addresses_to_trim_case_drain(list_addr, entry.length - addrs.len(), journal) {
                        Ok(pending_deallocations) => Ok(TrimAction::Drain{ pending_deallocations }),
                        Err(KvError::CRCMismatch) => Err(KvError::CRCMismatch),
                        _ => { assert(false); Err(KvError::InternalError) },
                    }
                }
            }
        }
    }

    pub exec fn trim(
        &mut self,
        list_addr: u64,
        trim_length: usize,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
            0 < trim_length,
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[list_addr];
                    &&& {
                           ||| new_list_addr == 0
                           ||| new_list_addr == list_addr
                           ||| !old(self)@.tentative.unwrap().m.contains_key(new_list_addr)
                    }
                    &&& trim_length <= old_list.len()
                    &&& new_list_addr == 0 ==> old_list.skip(trim_length as int) == Seq::<L>::empty()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().trim(list_addr, new_list_addr, trim_length as int)),
                        ..old(self)@
                    })
                    &&& new_list_addr != 0 ==> self.validate_list_addr(new_list_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    &&& self@ == old(self)@
                    &&& trim_length > upper_bound
                    &&& upper_bound == old(self)@.tentative.unwrap().m[list_addr].len()
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
        self.trim_now(list_addr, trim_length, journal, Tracked(perm))
    }

    pub exec fn trim_now(
        &mut self,
        list_addr: u64,
        trim_length: usize,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
            0 < trim_length,
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[list_addr];
                    &&& {
                           ||| new_list_addr == 0
                           ||| new_list_addr == list_addr
                           ||| !old(self)@.tentative.unwrap().m.contains_key(new_list_addr)
                    }
                    &&& trim_length <= old_list.len()
                    &&& new_list_addr == 0 ==> old_list.skip(trim_length as int) == Seq::<L>::empty()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().trim(list_addr, new_list_addr, trim_length as int)),
                        ..old(self)@
                    })
                    &&& new_list_addr != 0 ==> self.validate_list_addr(new_list_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    &&& self@ == old(self)@
                    &&& trim_length > upper_bound
                    &&& upper_bound == old(self)@.tentative.unwrap().m[list_addr].len()
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
            self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            broadcast use group_hash_axioms;
        }

        let action = match self.determine_action(list_addr, trim_length, journal) {
            Ok(act) => act,
            Err(KvError::CRCMismatch) => {
                self.must_abort = Ghost(true);
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            _ => {
                assert(false);
                return Err(KvError::InternalError);
            },
        };

        let ghost old_iv = self.internal_view();
        let ghost new_iv = old_iv.trim(list_addr, trim_length as int);
        let ghost g_action = action;
        match action {
            TrimAction::Delete => {
                match self.delete(list_addr, journal, Tracked(perm)) {
                    Ok(()) => {
                        assert(old(self)@.tentative.unwrap().m[list_addr].len() == trim_length);
                        assert(old(self)@.tentative.unwrap().m[list_addr].skip(trim_length as int) =~= Seq::<L>::empty());
                        return Ok(0);
                    },
                    Err(e) => {
                        return Err(e);
                    },
                };
            },
            TrimAction::Modify{ mut pending_deallocations, new_head } => {
                self.tentative_list_addrs = Ghost(new_iv.tentative_list_addrs);
                self.tentative_mapping = Ghost(new_iv.tentative_mapping);
                self.row_info = Ghost(new_iv.row_info);
                let old_entry = match self.m.remove(&list_addr) {
                    Some(e) => e,
                    None => { assert(false); return Err(KvError::InternalError); },
                };
                let (durable_entry, new_entry) = old_entry.trim(new_head, trim_length, self.modifications.len());
                self.m.insert(new_head, new_entry);
                self.deletes_inverse = Ghost(new_iv.deletes_inverse);
                self.deletes.push(durable_entry);
                self.modifications.push(Some(new_head));
                self.pending_deallocations.append(&mut pending_deallocations);
                assert(self.internal_view() =~= g_action.apply(old_iv, list_addr, trim_length as int));
                assert(self.internal_view() == old_iv.trim(list_addr, trim_length as int)) by {
                    g_action.lemma_action_works(old_iv, list_addr, trim_length as int, self.sm);
                }
                proof {
                    old_iv.lemma_trim_works(list_addr, trim_length as int, old(self).sm);
                }
                return Ok(new_head);
            },
            TrimAction::Advance{ mut pending_deallocations, new_head } => {
                self.tentative_list_addrs = Ghost(new_iv.tentative_list_addrs);
                self.tentative_mapping = Ghost(new_iv.tentative_mapping);
                self.row_info = Ghost(new_iv.row_info);
                let old_entry = match self.m.remove(&list_addr) {
                    Some(e) => e,
                    None => { assert(false); return Err(KvError::InternalError); },
                };
                let which_modification = match old_entry {
                    ListTableEntry::Modified{ which_modification, .. } => which_modification,
                    _ => { assert(false); return Err(KvError::InternalError); },
                };
                let (durable_entry, new_entry) = old_entry.trim(new_head, trim_length, self.modifications.len());
                self.m.insert(new_head, new_entry);
                self.modifications.set(which_modification, Some(new_head));
                self.pending_deallocations.append(&mut pending_deallocations);
                assert(self.internal_view() =~= g_action.apply(old_iv, list_addr, trim_length as int));
                assert(self.internal_view() == old_iv.trim(list_addr, trim_length as int)) by {
                    g_action.lemma_action_works(old_iv, list_addr, trim_length as int, self.sm);
                }
                proof {
                    old_iv.lemma_trim_works(list_addr, trim_length as int, old(self).sm);
                }
                return Ok(new_head);
            },
            _ => {},
        }

        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

