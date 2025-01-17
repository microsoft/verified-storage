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

broadcast use vstd::std_specs::hash::group_hash_axioms;

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn read(&self, k: &K, jv: Ghost<JournalView>) -> (result: Option<(u64, KeyTableRowMetadata)>)
        requires
            self.valid(jv@),
            self@.tentative.is_some(),
        ensures
            match result {
                None => !self@.tentative.unwrap().key_info.contains_key(*k),
                Some((key_addr, rm)) => {
                    let tentative = self@.tentative.unwrap();
                    &&& tentative.key_info.contains_key(*k)
                    &&& tentative.key_info[*k] == rm
                    &&& self.key_corresponds_to_key_addr(*k, key_addr)
                },
            }
    {
        match self.m.get(k) {
            None => None,
            Some(concrete_key_info) => Some((concrete_key_info.row_addr, concrete_key_info.rm)),
        }
    }

    proof fn lemma_writing_to_free_slot_maintains_internal_view_consistency(
        iv: KeyInternalView<K>,
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: KeyTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        start: int,
        end: int,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size,
            seqs_match_except_in_range(s1, s2, start, end),
        ensures
            iv.consistent_with_state(s2, sm),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    }

    proof fn lemma_writing_to_free_slot_doesnt_change_recovery(
        iv: KeyInternalView<K>,
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: KeyTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
        start: int,
        end: int,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size,
            seqs_match_except_in_range(s1, s2, start, end),
        ensures
            iv.consistent_with_state(s2, sm),
            Self::recover(s2, sm) == Self::recover(s1, sm),
    {
        Self::lemma_writing_to_free_slot_maintains_internal_view_consistency(iv, s1, s2, sm, free_list_pos,
                                                                             row_addr, start, end);
        iv.memory_mapping.as_recovery_mapping().lemma_corresponds_implies_equals_new(s1, sm);
        iv.memory_mapping.as_recovery_mapping().lemma_corresponds_implies_equals_new(s2, sm);
    }

    proof fn lemma_writing_to_free_slot_doesnt_change_recovery_forall(
        iv: KeyInternalView<K>,
        s1: Seq<u8>,
        sm: KeyTableStaticMetadata,
        free_list_pos: int,
        row_addr: u64,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(s1, sm),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
        ensures
            forall|s2: Seq<u8>, start: int, end: int| {
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& #[trigger] seqs_match_except_in_range(s1, s2, start, end)
            } ==> {
                &&& iv.consistent_with_state(s2, sm)
                &&& Self::recover(s2, sm) == Self::recover(s1, sm)
            }
    {
        assert forall|s2: Seq<u8>, start: int, end: int| {
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& #[trigger] seqs_match_except_in_range(s1, s2, start, end)
            } implies {
                &&& iv.consistent_with_state(s2, sm)
                &&& Self::recover(s2, sm) == Self::recover(s1, sm)
            } by {
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, s1, s2, sm, free_list_pos,
                                                                    row_addr, start, end);
        }
    }

    proof fn lemma_writing_to_free_slot_has_permission_forall(
        iv: KeyInternalView<K>,
        durable_state: Seq<u8>,
        sm: KeyTableStaticMetadata,
        constants: JournalConstants,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &TrustedKvPermission,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(durable_state, sm),
            ({
                &&& Journal::<TrustedKvPermission, PM>::recover(durable_state) matches Some(j)
                &&& j.constants == constants
                &&& j.state == durable_state
            }),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= durable_state.len(),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, durable_state, constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(durable_state, s, start, end)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
                &&& j.constants == constants
                &&& j.state == s
            } ==> {
                &&& Self::state_equivalent_for_me_specific(s, durable_state, constants, sm)
                &&& perm.check_permission(s)
            }
    {
        assert forall|s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(durable_state, s, start, end)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
                &&& j.constants == constants
                &&& j.state == s
            } implies {
                &&& Self::state_equivalent_for_me_specific(s, durable_state, constants, sm)
                &&& perm.check_permission(s)
            } by
        {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, durable_state, s, sm, free_list_pos,
                                                                    row_addr, start, end);
            assert(Self::state_equivalent_for_me_specific(s, durable_state, constants, sm));
        }
    }

    proof fn lemma_writing_to_free_slot_has_permission_later_forall(
        iv: KeyInternalView<K>,
        durable_state1: Seq<u8>,
        durable_state2: Seq<u8>,
        sm: KeyTableStaticMetadata,
        constants: JournalConstants,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &TrustedKvPermission,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(durable_state1, sm),
            iv.consistent_with_state(durable_state2, sm),
            ({
                &&& Journal::<TrustedKvPermission, PM>::recover(durable_state1) matches Some(j)
                &&& j.constants == constants
                &&& j.state == durable_state1
            }),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= durable_state1.len(),
            Self::recover(durable_state1, sm) is Some,
            Self::state_equivalent_for_me_specific(durable_state2, durable_state1, constants, sm),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, durable_state1, constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(durable_state2, s, start, end)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
                &&& j.constants == constants
                &&& j.state == s
            } ==> {
                &&& Self::state_equivalent_for_me_specific(s, durable_state1, constants, sm)
                &&& perm.check_permission(s)
            },
    {
        assert forall|s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(durable_state2, s, start, end)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
                &&& j.constants == constants
                &&& j.state == s
            } implies {
                &&& Self::state_equivalent_for_me_specific(s, durable_state1, constants, sm)
                &&& perm.check_permission(s)
            } by {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, durable_state2, s, sm, free_list_pos,
                                                                    row_addr, start, end);
        }
    }
    
    pub exec fn create(
        &mut self,
        k: &K,
        item_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            !old(self)@.tentative.unwrap().key_info.contains_key(*k),
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create(*k, item_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        proof {
            journal.lemma_valid_implications();
            self.lemma_valid_implications(journal@);
        }

        let key_addr = match self.free_list.pop() {
            None => { self.must_abort = Ghost(true); return Err(KvError::OutOfSpace); },
            Some(a) => a,
        };

        assert(self.memory_mapping@.row_info[key_addr] is InFreeList);
        proof {
            let ghost iv = old(self).internal_view().apply_undo_records(old(self).undo_records@, old(self).sm).unwrap();
            let ghost free_list_pos = self.free_list@.len();
            assert(0 <= free_list_pos < iv.free_list.len() && iv.free_list[free_list_pos as int] == key_addr) by {
                old(self).internal_view().lemma_apply_undo_records_only_appends_to_free_list(
                    old(self).undo_records@, old(self).sm
                );
            }
            Self::lemma_writing_to_free_slot_has_permission_later_forall(
                iv,
                journal@.durable_state,
                journal@.durable_state,
                old(self).sm,
                journal@.constants,
                free_list_pos as int,
                key_addr,
                perm
            );
        }

        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn delete(
        &mut self,
        k: &K,
        key_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().delete(*k)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_item(
        &mut self,
        k: &K,
        key_addr: u64,
        item_addr: u64,
        current_list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            old(self)@.tentative.unwrap().key_info[*k].list_addr == current_list_addr,
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_item(*k, item_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_list(
        &mut self,
        k: &K,
        key_addr: u64,
        current_item_addr: u64,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            old(self)@.tentative.unwrap().key_info[*k].item_addr == current_item_addr,
            !old(self)@.tentative.unwrap().list_addrs().contains(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_list(*k, list_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_item_and_list(
        &mut self,
        k: &K,
        key_addr: u64,
        item_addr: u64,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            !old(self)@.tentative.unwrap().list_addrs().contains(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_item_and_list(*k, item_addr, list_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

