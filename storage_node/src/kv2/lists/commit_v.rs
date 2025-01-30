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
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}
impl<L> ListInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn apply_change(self, tentative_list_addr: u64) -> Self
    {
        if self.m.contains_key(tentative_list_addr) {
            let new_entry = self.m[tentative_list_addr].as_tentative();
            Self {
                m: self.m.insert(tentative_list_addr, new_entry),
                ..self
            }
        } else {
            self
        }
    }

    pub(super) open spec fn apply_last_change(self) -> Self
        recommends
            0 < self.changes.len(),
    {
        let changed_self = match self.changes.last() {
            ListTableTentativeChange::Updated{ tentative_list_addr } =>
                self.apply_change(tentative_list_addr),
            ListTableTentativeChange::Created{ tentative_list_addr } =>
                self.apply_change(tentative_list_addr),
            ListTableTentativeChange::Deleted{ .. } =>
                self
        };
        Self {
            changes: self.changes.drop_last(),
            ..changed_self
        }
    }

    pub(super) open spec fn apply_changes(self) -> Self
        decreases
            self.changes.len(),
    {
        if self.changes.len() == 0 {
            self
        } else {
            self.apply_last_change().apply_changes()
        }
    }

    pub(super) open spec fn update_row_info_to_reflect_commit(self) -> Self
    {
        let new_row_info =
            Map::<u64, ListRowDisposition<L>>::new(
                |row_addr: u64| self.row_info.contains_key(row_addr),
                |row_addr: u64| match self.row_info[row_addr] {
                    ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                        ListRowDisposition::<L>::NowhereFree{ element },
                    ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + pos },
                    ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + dealloc_pos },
                    _ => self.row_info[row_addr],
                },
            );
        Self {
            row_info: new_row_info,
            free_list: self.free_list + self.pending_deallocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
            ..self
        }
    }

    pub(super) open spec fn commit(self) -> Self
    {
        let self2 = self.apply_changes();
        let self3 = self2.update_row_info_to_reflect_commit();
        Self {
            durable_changes: Map::<u64, usize>::empty(),
            durable_list_addrs: self3.tentative_list_addrs,
            durable_mapping: self3.tentative_mapping,
            ..self3
        }
    }

    proof fn lemma_apply_changes_empties_changes(self)
        ensures
            self.apply_changes().changes.len() == 0,
        decreases
            self.changes.len(),
    {
        if self.changes.len() > 0 {
            let new_self = self.apply_last_change();
            new_self.lemma_apply_changes_empties_changes();
        }
    }

    proof fn lemma_apply_changes_maintains_entry_durable(self, list_addr: u64)
        requires
            self.m.contains_key(list_addr),
            self.m[list_addr] is Durable,
        ensures
            self.apply_changes().m.contains_key(list_addr),
            self.apply_changes().m[list_addr] is Durable,
        decreases
            self.changes.len(),
    {
        if self.changes.len() > 0 {
            let new_self = self.apply_last_change();
            new_self.lemma_apply_changes_maintains_entry_durable(list_addr);
        }
    }

    proof fn lemma_apply_changes_ensures_entry_durable(
        self,
        which_change: int,
        list_addr: u64,
        sm: ListTableStaticMetadata
    )
        requires
            0 <= which_change < self.changes.len(),
            ({
                ||| self.changes[which_change] == (ListTableTentativeChange::Updated{ tentative_list_addr: list_addr })
                ||| self.changes[which_change] == (ListTableTentativeChange::Created{ tentative_list_addr: list_addr })
            }),
            forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) ==>
                self.m.contains_key(list_addr),
            self.m.contains_key(list_addr),
            self.tentative_mapping.list_info.contains_key(list_addr),
        ensures
            self.apply_changes().m.contains_key(list_addr),
            self.apply_changes().m[list_addr] is Durable,
        decreases
            self.changes.len(),
    {
        assert(self.m.contains_key(list_addr));
        let new_self = self.apply_last_change();
        if which_change == self.changes.len() - 1 {
            new_self.lemma_apply_changes_maintains_entry_durable(list_addr);
        }
        else {
            new_self.lemma_apply_changes_ensures_entry_durable(which_change, list_addr, sm);
        }
    }

    proof fn lemma_commit_ensures_entry_durable(self, list_addr: u64, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
            self.tentative_mapping.list_info.contains_key(list_addr),
        ensures
            self.commit().m.contains_key(list_addr),
            self.commit().m[list_addr] is Durable,
    {
        match self.m[list_addr] {
            ListTableEntryView::Durable{ .. } =>
                self.lemma_apply_changes_maintains_entry_durable(list_addr),
            ListTableEntryView::Created{ which_change, .. } =>
                self.lemma_apply_changes_ensures_entry_durable(which_change as int, list_addr, sm),
            ListTableEntryView::Updated{ which_change, .. } =>
                self.lemma_apply_changes_ensures_entry_durable(which_change as int, list_addr, sm),
            ListTableEntryView::TrimmedAndOrAppended{ which_change, .. } =>
                self.lemma_apply_changes_ensures_entry_durable(which_change as int, list_addr, sm),
        }
    }

    proof fn lemma_commit_ensures_all_entries_durable(self, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
        ensures
            forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) ==> {
                &&& self.commit().m.contains_key(list_addr)
                &&& self.commit().m[list_addr] is Durable
            },
    {
        assert forall|list_addr: u64| #[trigger] self.tentative_mapping.list_info.contains_key(list_addr) implies {
            &&& self.commit().m.contains_key(list_addr)
            &&& self.commit().m[list_addr] is Durable
        } by {
            self.lemma_commit_ensures_entry_durable(list_addr, sm);
        }
    }

    proof fn lemma_commit_maintains_tentative_info(self)
        ensures
            self.commit().tentative_list_addrs == self.tentative_list_addrs,
            self.commit().tentative_mapping == self.tentative_mapping,
        decreases
            self.changes.len(),
    {
        if self.changes.len() > 0 {
            let new_self = self.apply_last_change();
            new_self.lemma_commit_maintains_tentative_info();
        }
    }

    pub(super) proof fn lemma_commit_works(self, s: Seq<u8>, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
            self.corresponds_to_tentative_state(s, sm),
        ensures
            self.commit().valid(sm),
            self.commit().corresponds_to_durable_state(s, sm),
    {
        let self2 = self.apply_changes();
        let self3 = self2.update_row_info_to_reflect_commit();
        let self4 = self.commit();
        self.lemma_apply_changes_empties_changes();
        self.lemma_commit_ensures_all_entries_durable(sm);
        self.lemma_commit_maintains_tentative_info();
        assume(false);
        assume(self4.m_consistent_with_durable_recovery_mapping());
        assert(self4.valid(sm));
        assume(false);
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn commit(
        &mut self,
        Ghost(jv_before_commit): Ghost<JournalView>,
        Ghost(jv_after_commit): Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_commit),
            old(self)@.tentative is Some,
            jv_before_commit.valid(),
            jv_after_commit.valid(),
            jv_after_commit.committed_from(jv_before_commit),
        ensures
            self.valid(jv_after_commit),
            self@ == (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }),
    {
        let ghost new_row_info =
            Map::<u64, ListRowDisposition<L>>::new(
                |row_addr: u64| self.row_info@.contains_key(row_addr),
                |row_addr: u64| match self.row_info@[row_addr] {
                    ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                        ListRowDisposition::<L>::NowhereFree{ element },
                    ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list@.len() + pos },
                    ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                        ListRowDisposition::<L>::InFreeList{ pos: self.free_list@.len() + dealloc_pos },
                    _ => self.row_info@[row_addr],
                },
            );
        self.row_info = Ghost(new_row_info);
        self.free_list.append(&mut self.pending_deallocations);
        self.pending_allocations.clear();
        self.durable_list_addrs = self.tentative_list_addrs;
        self.durable_mapping = self.tentative_mapping;

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;

        assert(self.valid(jv_after_commit)) by {
            assert(self.sm.valid::<L>());
            assume(self.internal_view().valid(self.sm));
            assume(self.internal_view().corresponds_to_durable_state(jv_after_commit.durable_state, self.sm));
            assume(self.internal_view().corresponds_to_durable_state(jv_after_commit.read_state, self.sm));
            assume(self.internal_view().corresponds_to_tentative_state(jv_after_commit.commit_state, self.sm));
            assume(self.internal_view().consistent_with_journaled_addrs(jv_after_commit.journaled_addrs, self.sm));
        }
        assert(self@ =~= (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }));
    }
}

}

