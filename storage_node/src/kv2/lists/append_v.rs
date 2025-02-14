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
use super::util_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

impl<L> ListTableEntryView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn append(self, new_row_addr: u64, new_element: L) -> Self
        recommends
            match self {
                ListTableEntryView::Durable{ summary } => false,
                ListTableEntryView::Modified{ summary, .. } => summary.length < usize::MAX,
            },
    {
        match self {
            ListTableEntryView::Modified{ which_modification, durable_head, summary, addrs, elements } =>
                ListTableEntryView::Modified{
                    which_modification,
                    durable_head,
                    summary: ListSummary{ tail: new_row_addr, length: (summary.length + 1) as usize,
                                          end_of_logical_range: new_element.end(), ..summary },
                    addrs: addrs.push(new_row_addr),
                    elements: elements.push(new_element),
                },
            _ => self,
        }
    }

    pub(super) open spec fn update_by_appending(self, which_modification: nat, new_row_addr: u64, new_element: L) -> Self
        recommends
            match self {
                ListTableEntryView::Durable{ summary } => summary.length < usize::MAX,
                _ => false,
            },
    {
        match self {
            ListTableEntryView::Durable{ summary } => {
                let new_summary = ListSummary{
                    tail: new_row_addr,
                    length: (summary.length + 1) as usize,
                    end_of_logical_range: new_element.end(),
                    ..summary
                };
                ListTableEntryView::Modified{
                    which_modification,
                    durable_head: summary.head,
                    summary: new_summary,
                    addrs: seq![new_row_addr],
                    elements: seq![new_element],
                }
            },
            _ => self,
        }
    }
}

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    // TODO: Once Verus supports complex `&mut` scenarios, take `&mut self` parameter instead of `self`.
    pub(super) exec fn append(self, new_row_addr: u64, new_element: L) -> (result: Self)
        requires
            match self {
                ListTableEntry::Modified{ summary, .. } => summary.length < usize::MAX,
                _ => false,
            },
        ensures
            result@ == self@.append(new_row_addr, new_element),
    {
        match self {
            ListTableEntry::Modified{ which_modification, durable_head, mut summary, mut addrs, mut elements } =>
            {
                summary.tail = new_row_addr;
                summary.length = summary.length + 1;
                summary.end_of_logical_range = new_element.end();
                addrs.push(new_row_addr);
                elements.push(new_element);
                ListTableEntry::Modified{ which_modification, durable_head, summary, addrs, elements }
            },
            _ => self,
        }
    }

    pub(super) exec fn update_by_appending(&self, which_modification: usize, new_row_addr: u64, new_element: L)
                                           -> (result: Self)
        requires
            match self {
                ListTableEntry::Durable{ summary } => summary.length < usize::MAX,
                _ => false,
            },
        ensures
            result@ == self@.update_by_appending(which_modification as nat, new_row_addr, new_element),
    {
        match self {
            ListTableEntry::Durable{ ref summary } => {
                let new_summary = ListSummary{
                    head: summary.head,
                    tail: new_row_addr,
                    length: (summary.length + 1) as usize,
                    end_of_logical_range: new_element.end(),
                };
                let addrs = vec![new_row_addr];
                let elements = vec![new_element];
                assert(addrs@ =~= seq![new_row_addr]);
                assert(elements@ =~= seq![new_element]);
                ListTableEntry::Modified{
                    which_modification,
                    durable_head: Ghost(summary.head@),
                    summary: new_summary,
                    addrs,
                    elements,
                }
            },
            _ => { assert(false); Self::default() },
        }
    }

}

impl<L> ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn append(self, list_addr: u64, new_row_addr: u64, new_element: L) -> Self
        recommends
            self.list_info.contains_key(list_addr),
            self.list_info[list_addr].len() < usize::MAX,
    {
        let old_addrs = self.list_info[list_addr];
        let former_tail_addr = old_addrs.last();
        let former_tail_new_info = ListRowRecoveryInfo::<L>{ next: new_row_addr, ..self.row_info[former_tail_addr] };
        let new_tail_info =
            ListRowRecoveryInfo::<L>{ element: new_element, head: list_addr, next: 0, pos: old_addrs.len() as int };
        let new_addrs = old_addrs.push(new_row_addr);
        let old_elements = self.list_elements[list_addr];
        let new_elements = old_elements.push(new_element);
        Self{
            row_info: self.row_info.insert(former_tail_addr, former_tail_new_info).insert(new_row_addr, new_tail_info),
            list_info: self.list_info.insert(list_addr, new_addrs),
            list_elements: self.list_elements.insert(list_addr, new_elements),
        }
    }

    pub(super) open spec fn create_singleton(self, list_addr: u64, element: L) -> Self
    {
        let info = ListRowRecoveryInfo::<L>{ element, head: list_addr, next: 0, pos: 0 };
        Self{
            row_info: self.row_info.insert(list_addr, info),
            list_info: self.list_info.insert(list_addr, seq![list_addr]),
            list_elements: self.list_elements.insert(list_addr, seq![element]),
        }
    }
}

// There are two main cases we have to deal with when appending:
// Case "durable": The list hasn't been modified at all this transaction, which we
//                 can tell from the fact that `self.m[list_addr] is Durable`.
// Case "modified": The list has already been modified during this transaction,
//                  which we can tell because `self.m[list_addr] is Modified`.

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn append_case_durable(self, list_addr: u64, new_element: L) -> Self
        recommends
            self.m.contains_key(list_addr),
            self.m[list_addr] is Durable,
    {
        let which_delete = self.deletes.len();
        let which_modification = self.modifications.len();
        let new_row_addr = self.free_list.last();
        let new_delete = self.m[list_addr]->Durable_summary;
        let summary = self.m[list_addr].update_by_appending(which_modification, new_row_addr, new_element);
        let disposition = ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };

        Self{
            tentative_mapping: self.tentative_mapping.append(list_addr, new_row_addr, new_element),
            row_info: self.row_info.insert(new_row_addr, disposition),
            m: self.m.insert(list_addr, summary),
            deletes_inverse: self.deletes_inverse.insert(list_addr, which_delete),
            deletes: self.deletes.push(new_delete),
            modifications: self.modifications.push(Some(list_addr)),
            free_list: self.free_list.drop_last(),
            pending_allocations: self.pending_allocations.push(new_row_addr),
            ..self
        }
    }

    pub(super) open spec fn append_case_modified(self, list_addr: u64, new_element: L) -> Self
        recommends
            self.m.contains_key(list_addr),
            !(self.m[list_addr] is Durable),
    {
        let new_row_addr = self.free_list.last();
        let summary = self.m[list_addr].append(new_row_addr, new_element);
        let disposition = ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };

        Self{
            tentative_mapping: self.tentative_mapping.append(list_addr, new_row_addr, new_element),
            row_info: self.row_info.insert(new_row_addr, disposition),
            m: self.m.insert(list_addr, summary),
            free_list: self.free_list.drop_last(),
            pending_allocations: self.pending_allocations.push(new_row_addr),
            ..self
        }
    }

    pub(super) open spec fn create_singleton(self, new_element: L) -> Self
    {
        let row_addr = self.free_list.last();
        let disposition = ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };
        let which_modification = self.modifications.len();
        let summary = ListSummary{
            head: row_addr,
            tail: row_addr,
            length: 1,
            end_of_logical_range: new_element.end()
        };
        let entry_view = ListTableEntryView::<L>::Modified{
            durable_head: 0,
            which_modification,
            summary,
            addrs: seq![row_addr],
            elements: seq![new_element],
        };

        Self{
            tentative_list_addrs: self.tentative_list_addrs.insert(row_addr),
            tentative_mapping: self.tentative_mapping.create_singleton(row_addr, new_element),
            row_info: self.row_info.insert(row_addr, disposition),
            modifications: self.modifications.push(Some(row_addr)),
            free_list: self.free_list.drop_last(),
            pending_allocations: self.pending_allocations.push(row_addr),
            m: self.m.insert(row_addr, entry_view),
            ..self
        }
    }

    pub(super) proof fn lemma_append_case_durable_works(
        self,
        list_addr: u64,
        new_element: L,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.valid(sm),
            0 < sm.start(),
            self.durable_mapping.internally_consistent(sm),
            self.tentative_mapping.internally_consistent(sm),
            self.free_list.len() > 0,
            self.m.contains_key(list_addr),
            match self.m[list_addr] {
                ListTableEntryView::Durable{ summary } => summary.length < usize::MAX,
                _ => false,
            },
        ensures
            self.append_case_durable(list_addr, new_element).valid(sm),
            self.append_case_durable(list_addr, new_element).tentative_mapping.as_snapshot() ==
                self.tentative_mapping.as_snapshot().append(list_addr, list_addr, new_element),
    {
        let new_self = self.append_case_durable(list_addr, new_element);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();

        let tail_row_addr = match self.m[list_addr] {
            ListTableEntryView::Durable{ summary } => summary.tail,
            _ => { assert(false); 0u64 },
        };
        let new_row_addr = self.free_list.last();

        assert(new_snapshot =~= old_snapshot.append(list_addr, list_addr, new_element));
        assert(new_row_addr > 0) by {
            broadcast use group_validate_row_addr;
        }

        match new_self.m[list_addr] {
            ListTableEntryView::Modified{ durable_head, summary, addrs, elements, .. } => {
                let durable_addrs = new_self.durable_mapping.list_info[durable_head];
                let durable_elements = new_self.durable_mapping.list_elements[durable_head];
                let tentative_addrs = new_self.tentative_mapping.list_info[list_addr];
                let tentative_elements = new_self.tentative_mapping.list_elements[list_addr];
                assert(tentative_addrs =~=
                       durable_addrs.skip(durable_addrs.len() - (summary.length - addrs.len())) + addrs);
                assert(tentative_elements =~=
                       durable_elements.skip(durable_elements.len() - (summary.length - elements.len())) +
                       elements);
            },
            _ => { assert(false); },
        }

        assert(self.append_case_durable(list_addr, new_element).tentative_mapping.as_snapshot() =~=
               self.tentative_mapping.as_snapshot().append(list_addr, list_addr, new_element));
    }

    pub(super) proof fn lemma_append_case_modified_works(
        self,
        list_addr: u64,
        new_element: L,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.valid(sm),
            0 < sm.start(),
            self.durable_mapping.internally_consistent(sm),
            self.tentative_mapping.internally_consistent(sm),
            self.free_list.len() > 0,
            self.m.contains_key(list_addr),
            match self.m[list_addr] {
                ListTableEntryView::Modified{ summary, .. } => summary.length < usize::MAX,
                _ => false,
            },
        ensures
            self.append_case_modified(list_addr, new_element).valid(sm),
            self.append_case_modified(list_addr, new_element).tentative_mapping.as_snapshot() ==
                self.tentative_mapping.as_snapshot().append(list_addr, list_addr, new_element),
    {
        let new_self = self.append_case_modified(list_addr, new_element);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();

        let tail_row_addr = match self.m[list_addr] {
            ListTableEntryView::Modified{ summary, .. } => summary.tail,
            _ => { assert(false); 0u64 },
        };
        let new_row_addr = self.free_list.last();

        assert(new_snapshot =~= old_snapshot.append(list_addr, list_addr, new_element));
        assert(new_row_addr > 0) by {
            broadcast use group_validate_row_addr;
        }

        match new_self.m[list_addr] {
            ListTableEntryView::Modified{ durable_head, summary, addrs, elements, .. } => {
                let durable_addrs = new_self.durable_mapping.list_info[durable_head];
                let durable_elements = new_self.durable_mapping.list_elements[durable_head];
                let tentative_addrs = new_self.tentative_mapping.list_info[list_addr];
                let tentative_elements = new_self.tentative_mapping.list_elements[list_addr];
                assert(tentative_addrs =~=
                       durable_addrs.skip(durable_addrs.len() - (summary.length - addrs.len())) + addrs);
                assert(tentative_elements =~=
                       durable_elements.skip(durable_elements.len() - (summary.length - elements.len())) +
                       elements);
            },
            _ => { assert(false); },
        }
    }

    pub(super) proof fn lemma_create_singleton_works(self, new_element: L, sm: ListTableStaticMetadata)
        requires
            sm.valid::<L>(),
            self.valid(sm),
            self.durable_mapping.internally_consistent(sm),
            self.tentative_mapping.internally_consistent(sm),
            self.free_list.len() > 0,
        ensures
            self.create_singleton(new_element).valid(sm),
            self.create_singleton(new_element).tentative_mapping.as_snapshot() ==
                self.tentative_mapping.as_snapshot().create_singleton(self.free_list.last(), new_element),
    {
        let new_self = self.create_singleton(new_element);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();
        let row_addr = self.free_list.last();
        let tentative_addrs = seq![row_addr];
        let tentative_elements = seq![new_element];
        let which_modification = self.modifications.len();

        assert(tentative_elements =~= new_self.tentative_mapping.list_elements[row_addr]);

        assert(forall|list_addr: u64| #[trigger] new_self.m.contains_key(list_addr) ==>
               list_addr == row_addr || self.m.contains_key(list_addr));

        assert forall|list_addr: u64| #[trigger] new_snapshot.m.contains_key(list_addr) implies {
                &&& old_snapshot.create_singleton(row_addr, new_element).m.contains_key(list_addr)
                &&& new_snapshot.m[list_addr] == old_snapshot.create_singleton(row_addr, new_element).m[list_addr]
            } by {
            assert(list_addr != row_addr ==> old_snapshot.m.contains_key(list_addr));
            assert(old_snapshot.create_singleton(row_addr, new_element).m.contains_key(list_addr));
            assert(new_snapshot.m[list_addr] =~= old_snapshot.create_singleton(row_addr, new_element).m[list_addr]);
        }

        assert(new_snapshot =~= old_snapshot.create_singleton(row_addr, new_element));
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    #[inline]
    exec fn append_case_durable(
        &mut self,
        list_addr: u64,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        new_row_addr: u64,
        entry: ListTableEntry<L>,
        Ghost(prev_self): Ghost<Self>,
        Ghost(prev_jv): Ghost<JournalView>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self) == (Self{
                free_list: old(self).free_list,
                m: old(self).m,
                ..prev_self
            }),
            prev_self.free_list@.len() > 0,
            old(self).free_list@ == prev_self.free_list@.drop_last(),
            old(self).m@ == prev_self.m@.remove(list_addr),
            new_row_addr == prev_self.free_list@.last(),
            prev_self.valid(prev_jv),
            old(journal).valid(),
            old(journal)@.remaining_capacity >= old(self).space_needed_to_journal_next,
            prev_self@.tentative is Some,
            prev_self@.tentative.unwrap().m.contains_key(list_addr),
            prev_self.internal_view().corresponds_to_durable_state(old(journal)@.durable_state, prev_self.sm),
            prev_self.internal_view().corresponds_to_durable_state(old(journal)@.read_state, prev_self.sm),
            old(journal)@.matches_except_in_range(prev_jv, old(self)@.sm.start() as int, old(self)@.sm.end() as int),
            old(journal)@ == (JournalView{
                durable_state: old(journal)@.durable_state,
                read_state: old(journal)@.read_state,
                commit_state: old(journal)@.commit_state,
                ..prev_jv
            }),
            new_row_addr == prev_self.free_list@.last(),
            forall|other_row_addr: u64| {
                &&& old(self).sm.table.validate_row_addr(other_row_addr)
                &&& other_row_addr != new_row_addr
            } ==> {
                &&& recover_object::<L>(old(journal)@.commit_state, other_row_addr + old(self).sm.row_element_start,
                                      other_row_addr + old(self).sm.row_element_crc_start)
                    == recover_object::<L>(prev_jv.commit_state, other_row_addr + old(self).sm.row_element_start,
                                           other_row_addr + old(self).sm.row_element_crc_start)
                &&& recover_object::<u64>(old(journal)@.commit_state, other_row_addr + old(self).sm.row_next_start,
                                        other_row_addr + old(self).sm.row_next_start + u64::spec_size_of())
                    == recover_object::<u64>(prev_jv.commit_state, other_row_addr + old(self).sm.row_next_start,
                                             other_row_addr + old(self).sm.row_next_start + u64::spec_size_of())
            },
            recover_object::<u64>(old(journal)@.commit_state, new_row_addr + old(self).sm.row_next_start,
                                  new_row_addr + old(self).sm.row_next_start + u64::spec_size_of()) == Some(0u64),
            recover_object::<L>(old(journal)@.commit_state, new_row_addr + old(self).sm.row_element_start,
                                new_row_addr + old(self).sm.row_element_crc_start) == Some(new_element),
            prev_self.m@.contains_key(list_addr),
            entry == prev_self.m[list_addr],
            match entry@ {
                ListTableEntryView::Durable{ summary } => {
                    &&& summary.length < usize::MAX
                    &&& new_element.start() >= summary.end_of_logical_range
                    &&& old(self).logical_range_gaps_policy is LogicalRangeGapsForbidden ==>
                           new_element.start() == summary.end_of_logical_range
                },
                _ => false,
            },
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(prev_jv, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    &&& new_list_addr != 0
                    &&& new_list_addr == list_addr || !prev_self@.tentative.unwrap().m.contains_key(new_list_addr)
                    &&& match self@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_element.start() >= end_of_range(prev_self@.tentative.unwrap().m[list_addr]),
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_element.start() == end_of_range(prev_self@.tentative.unwrap().m[list_addr]),
                    }
                    &&& self@ == (ListTableView {
                        tentative: Some(prev_self@.tentative.unwrap().append(list_addr, new_list_addr, new_element)),
                        ..prev_self@
                    })
                    &&& self.validate_list_addr(new_list_addr)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..prev_self@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..prev_self@
                    })
                },
                _ => false,
            }
    {
        proof {
            journal.lemma_valid_implications();
            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use group_hash_axioms;
            broadcast use broadcast_journal_view_matches_in_range_transitive;
        }

        let tail_row_addr = match &entry {
            ListTableEntry::<L>::Durable{ summary } => summary.tail,
            _ => { assert(false); 0u64 },
        };
        assert(tail_row_addr == self.tentative_mapping@.list_info[list_addr].last());
        assert(self.sm.table.validate_row_addr(tail_row_addr));

        let ghost which_delete = self.deletes@.len();
        let which_modification = self.modifications.len();

        self.tentative_mapping = Ghost(self.tentative_mapping@.append(list_addr, new_row_addr, new_element));
        let ghost disposition =
            ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations@.len() as nat };
        self.row_info = Ghost(self.row_info@.insert(new_row_addr, disposition));
        let new_entry = entry.update_by_appending(which_modification, new_row_addr, new_element);
        let new_delete = entry.unwrap_durable();
        self.m.insert(list_addr, new_entry);
        self.deletes_inverse = Ghost(self.deletes_inverse@.insert(list_addr, which_delete));
        self.deletes.push(new_delete);
        self.modifications.push(Some(list_addr));
        self.pending_allocations.push(new_row_addr);

        assert(self.internal_view() =~= prev_self.internal_view().append_case_durable(list_addr, new_element));
        proof {
            prev_self.internal_view().lemma_append_case_durable_works(list_addr, new_element, prev_self.sm);
        }

        let next_addr = tail_row_addr + self.sm.row_next_start;
        let next_crc = calculate_crc(&new_row_addr);

        let mut bytes_to_write = Vec::<u8>::new();
        extend_vec_u8_from_slice(&mut bytes_to_write, new_row_addr.as_byte_slice());
        extend_vec_u8_from_slice(&mut bytes_to_write, next_crc.as_byte_slice());

        match journal.journal_write(next_addr, bytes_to_write) {
            Ok(()) => {},
            _ => {
                assert(false);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        }

        proof {
            lemma_writing_next_and_crc_together_effect_on_recovery::<L>(
                old(journal)@.commit_state, journal@.commit_state, tail_row_addr, new_row_addr, self.sm
            );
        }

        Ok(list_addr)
    }

    #[inline]
    exec fn append_case_modified(
        &mut self,
        list_addr: u64,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        new_row_addr: u64,
        entry: ListTableEntry<L>,
        Ghost(prev_self): Ghost<Self>,
        Ghost(prev_jv): Ghost<JournalView>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self) == (Self{
                free_list: old(self).free_list,
                m: old(self).m,
                ..prev_self
            }),
            prev_self.free_list@.len() > 0,
            old(self).free_list@ == prev_self.free_list@.drop_last(),
            old(self).m@ == prev_self.m@.remove(list_addr),
            new_row_addr == prev_self.free_list@.last(),
            prev_self.valid(prev_jv),
            old(journal).valid(),
            old(journal)@.remaining_capacity >= old(self).space_needed_to_journal_next,
            prev_self@.tentative is Some,
            prev_self@.tentative.unwrap().m.contains_key(list_addr),
            prev_self.internal_view().corresponds_to_durable_state(old(journal)@.durable_state, prev_self.sm),
            prev_self.internal_view().corresponds_to_durable_state(old(journal)@.read_state, prev_self.sm),
            old(journal)@.matches_except_in_range(prev_jv, old(self)@.sm.start() as int, old(self)@.sm.end() as int),
            old(journal)@ == (JournalView{
                durable_state: old(journal)@.durable_state,
                read_state: old(journal)@.read_state,
                commit_state: old(journal)@.commit_state,
                ..prev_jv
            }),
            new_row_addr == prev_self.free_list@.last(),
            forall|other_row_addr: u64| {
                &&& old(self).sm.table.validate_row_addr(other_row_addr)
                &&& other_row_addr != new_row_addr
            } ==> {
                &&& recover_object::<L>(old(journal)@.commit_state, other_row_addr + old(self).sm.row_element_start,
                                      other_row_addr + old(self).sm.row_element_crc_start)
                    == recover_object::<L>(prev_jv.commit_state, other_row_addr + old(self).sm.row_element_start,
                                           other_row_addr + old(self).sm.row_element_crc_start)
                &&& recover_object::<u64>(old(journal)@.commit_state, other_row_addr + old(self).sm.row_next_start,
                                        other_row_addr + old(self).sm.row_next_start + u64::spec_size_of())
                    == recover_object::<u64>(prev_jv.commit_state, other_row_addr + old(self).sm.row_next_start,
                                             other_row_addr + old(self).sm.row_next_start + u64::spec_size_of())
            },
            recover_object::<u64>(old(journal)@.commit_state, new_row_addr + old(self).sm.row_next_start,
                                  new_row_addr + old(self).sm.row_next_start + u64::spec_size_of()) == Some(0u64),
            recover_object::<L>(old(journal)@.commit_state, new_row_addr + old(self).sm.row_element_start,
                                new_row_addr + old(self).sm.row_element_crc_start) == Some(new_element),
            prev_self.m@.contains_key(list_addr),
            entry == prev_self.m[list_addr],
            match entry@ {
                ListTableEntryView::Modified{ summary, .. } => {
                    &&& summary.length < usize::MAX
                    &&& new_element.start() >= summary.end_of_logical_range
                    &&& old(self).logical_range_gaps_policy is LogicalRangeGapsForbidden ==>
                           new_element.start() == summary.end_of_logical_range
                },
                _ => false,
            },
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(prev_jv, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    &&& new_list_addr != 0
                    &&& new_list_addr == list_addr || !prev_self@.tentative.unwrap().m.contains_key(new_list_addr)
                    &&& match self@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_element.start() >= end_of_range(prev_self@.tentative.unwrap().m[list_addr]),
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_element.start() == end_of_range(prev_self@.tentative.unwrap().m[list_addr]),
                    }
                    &&& self@ == (ListTableView {
                        tentative: Some(prev_self@.tentative.unwrap().append(list_addr, new_list_addr, new_element)),
                        ..prev_self@
                    })
                    &&& self.validate_list_addr(new_list_addr)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..prev_self@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..prev_self@
                    })
                },
                _ => false,
            }
    {
        proof {
            journal.lemma_valid_implications();
            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use group_hash_axioms;
            broadcast use broadcast_journal_view_matches_in_range_transitive;
        }

        let tail_row_addr = match &entry {
            ListTableEntry::<L>::Modified{ summary, .. } => summary.tail,
            _ => { assert(false); 0u64 },
        };
        assert(tail_row_addr == self.tentative_mapping@.list_info[list_addr].last());
        assert(self.sm.table.validate_row_addr(tail_row_addr));

        self.tentative_mapping = Ghost(self.tentative_mapping@.append(list_addr, new_row_addr, new_element));
        let ghost disposition =
            ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations@.len() as nat };
        self.row_info = Ghost(self.row_info@.insert(new_row_addr, disposition));
        let new_entry = entry.append(new_row_addr, new_element);
        self.m.insert(list_addr, new_entry);
        self.pending_allocations.push(new_row_addr);

        assert(self.internal_view() =~= prev_self.internal_view().append_case_modified(list_addr, new_element));
        proof {
            prev_self.internal_view().lemma_append_case_modified_works(list_addr, new_element, prev_self.sm);
        }

        let next_addr = tail_row_addr + self.sm.row_next_start;
        let next_crc = calculate_crc(&new_row_addr);

        let mut bytes_to_write = Vec::<u8>::new();
        extend_vec_u8_from_slice(&mut bytes_to_write, new_row_addr.as_byte_slice());
        extend_vec_u8_from_slice(&mut bytes_to_write, next_crc.as_byte_slice());

        match journal.journal_write(next_addr, bytes_to_write) {
            Ok(()) => {},
            _ => {
                assert(false);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        }

        proof {
            lemma_writing_next_and_crc_together_effect_on_recovery::<L>(
                old(journal)@.commit_state, journal@.commit_state, tail_row_addr, new_row_addr, self.sm
            );
        }

        Ok(list_addr)
    }

    #[inline]
    exec fn write_tail_to_free_slot(
        &self,
        new_element: L,
        row_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
        Ghost(prev_self): Ghost<Self>,
    )
        requires
            self == (Self{ free_list: self.free_list, m: self.m, ..prev_self }),
            prev_self.free_list@.len() > 0,
            self.free_list@ == prev_self.free_list@.drop_last(),
            row_addr == prev_self.free_list@.last(),
            prev_self.valid(old(journal)@),
            prev_self@.tentative is Some,
            old(journal).valid(),
            forall|s: Seq<u8>| prev_self.state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            journal@.journaled_addrs == old(journal)@.journaled_addrs,
            journal@.remaining_capacity == old(journal)@.remaining_capacity,
            self.internal_view().corresponds_to_durable_state(journal@.durable_state, self.sm),
            self.internal_view().corresponds_to_durable_state(journal@.read_state, self.sm),
            forall|other_row_addr: u64| {
                &&& self.sm.table.validate_row_addr(other_row_addr)
                &&& other_row_addr != row_addr
            } ==> {
                &&& recover_object::<L>(journal@.commit_state, other_row_addr + self.sm.row_element_start,
                                      other_row_addr + self.sm.row_element_crc_start)
                    == recover_object::<L>(old(journal)@.commit_state, other_row_addr + self.sm.row_element_start,
                                           other_row_addr + self.sm.row_element_crc_start)
                &&& recover_object::<u64>(journal@.commit_state, other_row_addr + self.sm.row_next_start,
                                        other_row_addr + self.sm.row_next_start + u64::spec_size_of())
                    == recover_object::<u64>(old(journal)@.commit_state, other_row_addr + self.sm.row_next_start,
                                             other_row_addr + self.sm.row_next_start + u64::spec_size_of())
            },
            recover_object::<L>(journal@.commit_state, row_addr + self.sm.row_element_start,
                                row_addr + self.sm.row_element_crc_start) == Some(new_element),
            recover_object::<u64>(journal@.commit_state, row_addr + self.sm.row_next_start,
                                  row_addr + self.sm.row_next_start + u64::spec_size_of()) == Some(0u64),
    {
        proof {
            prev_self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            assert(prev_self@.durable.m.dom() =~= prev_self.internal_view().durable_list_addrs);
            Self::lemma_writing_to_free_slot_has_permission_later_forall(
                prev_self.internal_view(),
                journal@,
                prev_self.sm,
                prev_self.free_list@.len() - 1,
                row_addr,
                perm
            );

            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use group_hash_axioms;
            broadcast use broadcast_journal_view_matches_in_range_transitive;
        }

        let element_addr = row_addr + self.sm.row_element_start;
        let element_crc_addr = row_addr + self.sm.row_element_crc_start;
        let element_crc = calculate_crc(&new_element);

        journal.write_object::<L>(element_addr, &new_element, Tracked(perm));
        journal.write_object::<u64>(element_crc_addr, &element_crc, Tracked(perm));

        let next_addr = row_addr + self.sm.row_next_start;
        let next_crc_addr = next_addr + size_of::<u64>() as u64;
        let next: u64 = 0;
        let next_crc = calculate_crc(&next);

        journal.write_object::<u64>(next_addr, &next, Tracked(perm));
        journal.write_object::<u64>(next_crc_addr, &next_crc, Tracked(perm));

        // Leverage postcondition of `lemma_writing_to_free_slot_has_permission_later_forall`
        // to conclude that `self` is still consistent with both the durable and read state
        // of the journal.
        assert(self.internal_view().corresponds_to_durable_state(journal@.durable_state, self.sm));
        assert(self.internal_view().corresponds_to_durable_state(journal@.read_state, self.sm));

        proof {
            lemma_writing_element_and_next_effect_on_recovery(
                old(journal)@.commit_state, journal@.commit_state, row_addr, new_element, 0u64, self.sm
            );
        }
    }

    pub exec fn append(
        &mut self,
        list_addr: u64,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    &&& new_list_addr != 0
                    &&& new_list_addr == list_addr || !old(self)@.tentative.unwrap().m.contains_key(new_list_addr)
                    &&& match self@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_element.start() >= end_of_range(old(self)@.tentative.unwrap().m[list_addr]),
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_element.start() == end_of_range(old(self)@.tentative.unwrap().m[list_addr]),
                    }
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().append(list_addr, new_list_addr, new_element)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_list_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_element.start() > end_of_range(old(self)@.tentative.unwrap().m[list_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[list_addr])
                },
                Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& new_element.start() < end_of_range(old(self)@.tentative.unwrap().m[list_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[list_addr])
                }
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
            assert(self@.durable.m.dom() =~= self.internal_view().durable_list_addrs);
            if self.free_list@.len() > 0 {
                Self::lemma_writing_to_free_slot_has_permission_later_forall(
                    self.internal_view(),
                    journal@,
                    self.sm,
                    self.free_list@.len() - 1,
                    self.free_list@.last(),
                    perm
                );
            }

            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use group_hash_axioms;
            broadcast use broadcast_journal_view_matches_in_range_transitive;
        }

        if self.free_list.len() == 0 {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        if journal.remaining_capacity() < self.space_needed_to_journal_next {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        let entry = match self.m.remove(&list_addr) {
            None => { assert(false); return Err(KvError::InternalError) },
            Some(e) => e,
        };

        let (length, end_of_valid_range) = match &entry {
            ListTableEntry::<L>::Modified{ ref summary, .. } =>
                (summary.length, summary.end_of_logical_range),
            ListTableEntry::<L>::Durable{ ref summary } =>
                (summary.length, summary.end_of_logical_range),
        };

        assert(length == self.tentative_mapping@.list_elements[list_addr].len());
        assert(end_of_valid_range == end_of_range(self.tentative_mapping@.list_elements[list_addr]));

        if length >= usize::MAX {
            self.m.insert(list_addr, entry);
            assert(self.internal_view() =~= old(self).internal_view());
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        if new_element.start() < end_of_valid_range {
            self.m.insert(list_addr, entry);
            assert(self.internal_view() =~= old(self).internal_view());
            return Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range});
        }

        match self.logical_range_gaps_policy {
            LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                if new_element.start() > end_of_valid_range {
                    self.m.insert(list_addr, entry);
                    assert(self.internal_view() =~= old(self).internal_view());
                    return Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range });
                },
            _ => {},
        }

        let row_addr = match self.free_list.pop() {
            None => { assert(false); 0u64 },
            Some(a) => a,
        };

        assert(row_addr == old(self).free_list@[old(self).free_list@.len() - 1]);

        self.write_tail_to_free_slot(new_element, row_addr, journal, Tracked(perm), Ghost(*old(self)));

        match entry {
            ListTableEntry::<L>::Durable{ .. } =>
                self.append_case_durable(list_addr, new_element, journal, row_addr, entry,
                                         Ghost(*old(self)), Ghost(old(journal)@)),
            ListTableEntry::<L>::Modified{ .. } =>
                self.append_case_modified(list_addr, new_element, journal, row_addr, entry,
                                          Ghost(*old(self)), Ghost(old(journal)@)),
        }
    }

    pub exec fn create_singleton(
        &mut self,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(journal).valid(),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    &&& new_row_addr != 0
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden ==>
                        new_element.start() == 0
                    &&& !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create_singleton(new_row_addr, new_element)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_element.start() != 0
                    &&& end_of_valid_range == 0
                }
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
            assert(self@.durable.m.dom() =~= self.internal_view().durable_list_addrs);

            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_hash_axioms;
        }

        match self.logical_range_gaps_policy {
            LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                if new_element.start() != 0 {
                    return Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range: 0 });
                },
            _ => {},
        }

        let row_addr = match self.free_list.pop() {
            None => {
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            Some(a) => a,
        };
        assert(old(self).free_list@[self.free_list@.len() as int] == row_addr);

        self.write_tail_to_free_slot(new_element, row_addr, journal, Tracked(perm), Ghost(*old(self)));

        self.tentative_list_addrs = Ghost(self.tentative_list_addrs@.insert(row_addr));
        self.tentative_mapping = Ghost(self.tentative_mapping@.create_singleton(row_addr, new_element));

        let ghost disposition =
            ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat };
        self.row_info = Ghost(self.row_info@.insert(row_addr, disposition));

        let which_modification = self.modifications.len();
        self.modifications.push(Some(row_addr));

        self.pending_allocations.push(row_addr);

        let addrs = vec![row_addr];
        let elements = vec![new_element];
        assert(addrs@ =~= seq![row_addr]);
        assert(elements@ =~= seq![new_element]);
        let summary = ListSummary{
            head: row_addr,
            tail: row_addr,
            length: 1,
            end_of_logical_range: new_element.end(),
        };
        let entry = ListTableEntry::<L>::Modified{
            which_modification,
            durable_head: Ghost(0),
            summary,
            addrs,
            elements,
        };
        self.m.insert(row_addr, entry);

        assert(self.internal_view() =~= old(self).internal_view().create_singleton(new_element));
        proof {
            old(self).internal_view().lemma_create_singleton_works(new_element, self.sm);
        }

        assert(self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create_singleton(row_addr, new_element)),
                        ..old(self)@
                    }));
        assert(self.valid(journal@));

        Ok(row_addr)
    }
}

}

