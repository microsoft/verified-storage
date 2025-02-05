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

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    proof fn lemma_writing_to_free_slot_doesnt_change_recovery(
        iv: ListTableInternalView<L>,
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: ListTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        start: int,
        end: int,
    )
        requires
            sm.valid::<L>(),
            iv.valid(sm),
            iv.corresponds_to_durable_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            row_addr <= start <= end <= row_addr + sm.table.row_size,
            seqs_match_except_in_range(s1, s2, start, end),
        ensures
            iv.corresponds_to_durable_state(s2, sm),
            Self::recover(s2, iv.durable_list_addrs, sm) == Self::recover(s1, iv.durable_list_addrs, sm),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(iv.row_info[row_addr] is InFreeList);
        assert(iv.corresponds_to_durable_state(s2, sm));
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s1, iv.durable_list_addrs, sm);
        iv.durable_mapping.lemma_corresponds_implies_equals_new(s2, iv.durable_list_addrs, sm);
        assert(Self::recover(s2, iv.durable_list_addrs, sm) =~= Self::recover(s1, iv.durable_list_addrs, sm));
    }

    proof fn lemma_writing_to_free_slot_has_permission_later_forall(
        iv: ListTableInternalView<L>,
        initial_durable_state: Seq<u8>,
        sm: ListTableStaticMetadata,
        constants: JournalConstants,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &TrustedKvPermission,
    )
        requires
            sm.valid::<L>(),
            iv.valid(sm),
            iv.corresponds_to_durable_state(initial_durable_state, sm),
            Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(initial_durable_state, constants),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= initial_durable_state.len(),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, iv.durable_list_addrs,
                                                                 initial_durable_state, constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, iv.durable_list_addrs,
                                                         initial_durable_state, constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(s, constants)
            } ==> {
                &&& Self::state_equivalent_for_me_specific(s, iv.durable_list_addrs,
                                                         initial_durable_state, constants, sm)
                &&& iv.corresponds_to_durable_state(s, sm)
                &&& perm.check_permission(s)
            },
    {
        let list_addrs = iv.durable_list_addrs;
        assert forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, list_addrs,
                                                         initial_durable_state, constants, sm)
                &&& iv.corresponds_to_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(s, constants)
            } implies {
                &&& Self::state_equivalent_for_me_specific(s, list_addrs, initial_durable_state, constants, sm)
                &&& iv.corresponds_to_durable_state(s, sm)
                &&& perm.check_permission(s)
            } by {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, current_durable_state, s, sm,
                                                                    free_list_pos, row_addr, start, end);
        }
    }

    pub exec fn append(
        &mut self,
        row_addr: u64,
        new_list_entry: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    &&& new_row_addr != 0
                    &&& new_row_addr == row_addr || !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& match self@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_list_entry.start() >= end_of_range(old(self)@.tentative.unwrap().m[row_addr]),
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_list_entry.start() == end_of_range(old(self)@.tentative.unwrap().m[row_addr]),
                    }
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().append(row_addr, new_row_addr, new_list_entry)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_entry.start() > end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                },
                Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& new_list_entry.start() < end_of_range(old(self)@.tentative.unwrap().m[row_addr])
                    &&& end_of_valid_range == end_of_range(old(self)@.tentative.unwrap().m[row_addr])
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
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn create_singleton(
        &mut self,
        new_list_entry: L,
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
                        new_list_entry.start() == 0
                    &&& !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create_singleton(new_row_addr, new_list_entry)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                    &&& self@ == old(self)@
                    &&& self@.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_entry.start() != 0
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
        }

        match self.logical_range_gaps_policy {
            LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                if new_list_entry.start() != 0 {
                    return Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range: 0 });
                },
            _ => {},
        }

        let free_list_len = self.free_list.len();
        if free_list_len == 0 {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        let free_index = self.free_list[free_list_len - 1];
        
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

