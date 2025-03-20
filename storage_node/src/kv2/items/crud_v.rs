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
use recover_v::*;
use std::collections::HashSet;
use std::hash::Hash;
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::slice::slice_to_vec;

verus! {

impl<Perm, PM, I> ItemTable<Perm, PM, I>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn read(&self, row_addr: u64, journal: &Journal<Perm, PM>) -> (result: Result<I, KvError>)
        requires
            journal.valid(),
            self.valid(journal@),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            match result {
                Ok(item) => self@.tentative.unwrap().m[row_addr] == item,
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        proof {
            self.lemma_valid_implications(journal@);
            broadcast use group_validate_row_addr;
        }

        match exec_recover_object::<PM, I>(journal.get_pm_region_ref(), row_addr + self.sm.row_item_start,
                                           row_addr + self.sm.row_item_crc_start) {
            Some(item) => Ok(item),
            None => Err(KvError::CRCMismatch),
        }
    }

    proof fn lemma_writing_to_free_slot_doesnt_change_recovery(
        iv: ItemTableInternalView<I>,
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: ItemTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        start: int,
        end: int,
    )
        requires
            sm.valid::<I>(),
            iv.valid(sm),
            iv.consistent_with_durable_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            row_addr <= start <= end <= row_addr + sm.table.row_size,
            seqs_match_except_in_range(s1, s2, start, end),
        ensures
            iv.consistent_with_durable_state(s2, sm),
            Self::recover(s2, iv.as_durable_snapshot().m.dom(), sm) ==
                Self::recover(s1, iv.as_durable_snapshot().m.dom(), sm),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(Self::recover(s2, iv.as_durable_snapshot().m.dom(), sm) =~=
               Self::recover(s1, iv.as_durable_snapshot().m.dom(), sm));
    }

    proof fn lemma_writing_to_free_slot_has_permission_later_forall(
        iv: ItemTableInternalView<I>,
        initial_durable_state: Seq<u8>,
        sm: ItemTableStaticMetadata,
        constants: JournalConstants,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &Perm,
    )
        requires
            sm.valid::<I>(),
            iv.valid(sm),
            iv.consistent_with_durable_state(initial_durable_state, sm),
            Journal::<Perm, PM>::state_recovery_idempotent(initial_durable_state, constants),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= initial_durable_state.len(),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, iv.as_durable_snapshot().m.dom(),
                                                                 initial_durable_state, constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, iv.as_durable_snapshot().m.dom(),
                                                         initial_durable_state, constants, sm)
                &&& iv.consistent_with_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<Perm, PM>::state_recovery_idempotent(s, constants)
            } ==> {
                &&& Self::state_equivalent_for_me_specific(s, iv.as_durable_snapshot().m.dom(),
                                                         initial_durable_state, constants, sm)
                &&& iv.consistent_with_durable_state(s, sm)
                &&& perm.check_permission(s)
            },
    {
        let item_addrs = iv.as_durable_snapshot().m.dom();
        assert forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, item_addrs,
                                                         initial_durable_state, constants, sm)
                &&& iv.consistent_with_durable_state(current_durable_state, sm)
                &&& row_addr <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<Perm, PM>::state_recovery_idempotent(s, constants)
            } implies {
                &&& Self::state_equivalent_for_me_specific(s, item_addrs, initial_durable_state, constants, sm)
                &&& iv.consistent_with_durable_state(s, sm)
                &&& perm.check_permission(s)
            } by {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, current_durable_state, s, sm,
                                                                    free_list_pos, row_addr, start, end);
        }
    }

    pub exec fn create(
        &mut self,
        item: &I,
        journal: &mut Journal<Perm, PM>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative.is_some(),
            old(journal).valid(),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            journal@.remaining_capacity == old(journal)@.remaining_capacity,
            match result {
                Ok(row_addr) => {
                    &&& self@ == (ItemTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create(row_addr, *item)),
                        used_slots: self@.used_slots,
                        ..old(self)@
                    })
                    &&& self@.used_slots <= old(self)@.used_slots + 1
                    &&& !old(self)@.tentative.unwrap().m.contains_key(row_addr)
                    &&& self.validate_item_addr(row_addr)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ItemTableView {
                        tentative: None,
                        ..old(self)@
                    })
                    &&& self@.used_slots == self@.sm.num_rows()
                },
                _ => false,
            },
    {
        proof {
            journal.lemma_valid_implications();
            self.lemma_valid_implications(journal@);
            if self.free_list@.len() > 0 {
                Self::lemma_writing_to_free_slot_has_permission_later_forall(
                    self.internal_view(),
                    journal@.durable_state,
                    self.sm,
                    journal@.constants,
                    self.free_list@.len() - 1,
                    self.free_list@.last(),
                    perm
                );
            }

            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_update_bytes_effect;
        }

        let row_addr = match self.free_list.pop() {
            None => {
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            Some(a) => a,
        };
        assert(old(self).free_list@[self.free_list@.len() as int] == row_addr);

        let item_addr = row_addr + self.sm.row_item_start;
        let item_crc_addr = row_addr + self.sm.row_item_crc_start;
        let item_crc = calculate_crc(item);

        journal.write_object::<I>(item_addr, &item, Tracked(perm));
        journal.write_object::<u64>(item_crc_addr, &item_crc, Tracked(perm));

        let ghost disposition =
            ItemRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() as nat, item: *item };
        self.row_info = Ghost(self.row_info@.insert(row_addr, disposition));
        self.pending_allocations.push(row_addr);
        assert(self@.durable =~= old(self)@.durable);
        assert(self@.tentative =~= Some(old(self)@.tentative.unwrap().create(row_addr, *item)));
        Ok(row_addr)
    }

    pub exec fn delete(
        &mut self,
        row_addr: u64,
        journal: &Journal<Perm, PM>,
    )
        requires
            old(self).valid(journal@),
            journal.valid(),
            old(self)@.tentative.is_some(),
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            self.valid(journal@),
            self@ == (ItemTableView {
                tentative: Some(old(self)@.tentative.unwrap().delete(row_addr)),
                ..old(self)@
            }),
    {
        let ghost new_pos = self.pending_deallocations@.len() as nat;
        let ghost disposition = match self.row_info@[row_addr] {
            ItemRowDisposition::NowhereFree{ item } =>
                ItemRowDisposition::InPendingDeallocationList{ pos: new_pos, item },
            ItemRowDisposition::InPendingAllocationList{ pos, item } =>
                 ItemRowDisposition::InBothPendingLists{ alloc_pos: pos, dealloc_pos: new_pos, item },
            _ => { assert(false); arbitrary() },
        };
        self.row_info = Ghost(self.row_info@.insert(row_addr, disposition));
        self.pending_deallocations.push(row_addr);
        assert(self@.durable =~= old(self)@.durable);
        assert(self@.tentative =~= Some(old(self)@.tentative.unwrap().delete(row_addr)));
    }

}

}
