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
use vstd::slice::slice_to_vec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

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
        broadcast use group_validate_row_addr;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        iv.memory_mapping.as_recovery_mapping().lemma_corresponds_implies_equals_new(s1, sm);
        iv.memory_mapping.as_recovery_mapping().lemma_corresponds_implies_equals_new(s2, sm);
    }

    proof fn lemma_writing_to_free_slot_has_permission_later_forall(
        iv: KeyInternalView<K>,
        initial_durable_state: Seq<u8>,
        sm: KeyTableStaticMetadata,
        constants: JournalConstants,
        free_list_pos: int,
        row_addr: u64,
        tracked perm: &TrustedKvPermission,
    )
        requires
            sm.valid::<K>(),
            iv.consistent_with_state(initial_durable_state, sm),
            Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(initial_durable_state, constants),
            0 <= free_list_pos < iv.free_list.len(),
            iv.free_list[free_list_pos] == row_addr,
            sm.table.validate_row_addr(row_addr),
            sm.table.end <= initial_durable_state.len(),
            forall|s: Seq<u8>| Self::state_equivalent_for_me_specific(s, initial_durable_state, constants, sm)
                ==> #[trigger] perm.check_permission(s),
        ensures
            forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, initial_durable_state,
                                                         constants, sm)
                &&& iv.consistent_with_state(current_durable_state, sm)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(s, constants)
            } ==> {
                &&& Self::state_equivalent_for_me_specific(s, initial_durable_state, constants, sm)
                &&& iv.consistent_with_state(s, sm)
                &&& perm.check_permission(s)
            },
    {
        assert forall|current_durable_state: Seq<u8>, s: Seq<u8>, start: int, end: int| {
                &&& #[trigger] seqs_match_except_in_range(current_durable_state, s, start, end)
                &&& Self::state_equivalent_for_me_specific(current_durable_state, initial_durable_state,
                                                         constants, sm)
                &&& iv.consistent_with_state(current_durable_state, sm)
                &&& row_addr + sm.row_metadata_start <= start <= end <= row_addr + sm.table.row_size
                &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(s, constants)
            } implies {
                &&& Self::state_equivalent_for_me_specific(s, initial_durable_state, constants, sm)
                &&& iv.consistent_with_state(s, sm)
                &&& perm.check_permission(s)
            } by {
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            Self::lemma_writing_to_free_slot_doesnt_change_recovery(iv, current_durable_state, s, sm,
                                                                    free_list_pos, row_addr, start, end);
        }
    }

    #[inline]
    exec fn create_step1(
        &mut self,
        k: &K,
        item_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            !old(self)@.tentative.unwrap().key_info.contains_key(*k),
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
        ensures
            self.inv(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            journal@.durable_state == old(journal)@.durable_state,
            match result {
                Ok(row_addr) => {
                    &&& 0 < self.free_list@.len()
                    &&& row_addr == self.free_list@.last()
                    &&& self == (Self{ status: Ghost(KeyTableStatus::Inconsistent), ..*old(self) })
                    &&& recover_cdb(journal@.commit_state, row_addr + self.sm.row_cdb_start) == Some(true)
                    &&& seqs_match_except_in_range(old(journal)@.commit_state, journal@.commit_state,
                                                 row_addr as int, row_addr + self.sm.table.row_size)
                    &&& journal@.journaled_addrs == old(journal)@.journaled_addrs +
                        Set::<int>::new(|i: int| row_addr + self.sm.row_cdb_start <= i
                                      < row_addr + self.sm.row_cdb_start + u64::spec_size_of())
                },
                Err(KvError::OutOfSpace) => {
                    &&& self.valid(journal@)
                    &&& self@ == (KeyTableView { tentative: None, ..old(self)@ })
                },
                _ => false,
            },
    {
        proof {
            journal.lemma_valid_implications();
            self.lemma_valid_implications(journal@);
            broadcast use pmcopy_axioms;
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_update_bytes_effect;
        }

        // Read the last element in the free list but don't pop it
        // yet, to maintain validity of our data structures in case
        // the journal doesn't have enouh space to write. We leave
        // it to our caller to pop that element from the free list.

        let free_list_len = self.free_list.len();
        let ghost free_list_pos = free_list_len - 1;
        if free_list_len == 0 {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }
        let row_addr = self.free_list[free_list_len - 1];

        let cdb_addr = row_addr + self.sm.row_cdb_start;
        let cdb = CDB_TRUE;
        let cdb_bytes = slice_to_vec(cdb.as_byte_slice());
        match journal.journal_write(cdb_addr, cdb_bytes) {
            Ok(()) => {},
            Err(JournalError::NotEnoughSpace) => {
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            _ => {
                assert(false);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        };

        self.status = Ghost(KeyTableStatus::Inconsistent);
        Ok(row_addr)
    }

    #[inline]
    exec fn create_step2(
        &self,
        k: &K,
        item_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        row_addr: u64,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    )
        requires
            self.inv(old(journal)@),
            self.status@ is Inconsistent,
            old(journal).valid(),
            self@.tentative is Some,
            !self@.tentative.unwrap().key_info.contains_key(*k),
            !self@.tentative.unwrap().item_addrs().contains(item_addr),
            forall|s: Seq<u8>| self.state_equivalent_for_me(s, old(journal)@) ==>
                #[trigger] perm.check_permission(s),
            0 < self.free_list@.len(),
            row_addr == self.free_list@.last(),
            forall|addr: int|
                row_addr + self.sm.row_metadata_start <= addr < row_addr + self.sm.table.row_size ==>
                !(#[trigger] old(journal)@.journaled_addrs.contains(addr)),
        ensures
            self.inv(journal@),
            journal.valid(),
            journal@.journaled_addrs == old(journal)@.journaled_addrs,
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            recover_object::<K>(journal@.commit_state, row_addr + self.sm.row_key_start,
                                row_addr + self.sm.row_key_crc_start as u64) == Some(*k),
            recover_object::<KeyTableRowMetadata>(
                journal@.commit_state, row_addr + self.sm.row_metadata_start,
                row_addr + self.sm.row_metadata_crc_start
            ) == Some(KeyTableRowMetadata{ item_addr, list_addr: 0 }),
            seqs_match_except_in_range(old(journal)@.commit_state, journal@.commit_state,
                                       row_addr + self.sm.row_metadata_start,
                                       row_addr + self.sm.table.row_size),
    {
        proof {
            journal.lemma_valid_implications();
            broadcast use pmcopy_axioms;
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_update_bytes_effect;
        }

        let ghost iv = self.internal_view().apply_undo_records(self.undo_records@, self.sm).unwrap();

        proof {
            let ghost free_list_pos = self.free_list@.len() - 1;
            assert(0 <= free_list_pos < iv.free_list.len() && iv.free_list[free_list_pos as int] == row_addr) by {
                self.internal_view().lemma_apply_undo_records_only_appends_to_free_list(
                    self.undo_records@, self.sm
                );
            }
            Self::lemma_writing_to_free_slot_has_permission_later_forall(
                iv,
                journal@.durable_state,
                self.sm,
                journal@.constants,
                free_list_pos as int,
                row_addr,
                perm
            );
        }

        let key_addr = row_addr + self.sm.row_key_start;
        journal.write_object(key_addr, k, Tracked(perm));
        let key_crc_addr = row_addr + self.sm.row_key_crc_start;
        let key_crc = calculate_crc(k);
        journal.write_object(key_crc_addr, &key_crc, Tracked(perm));

        let rm = KeyTableRowMetadata{ item_addr, list_addr: 0 };
        let metadata_addr = row_addr + self.sm.row_metadata_start;
        journal.write_object(metadata_addr, &rm, Tracked(perm));
        let rm_crc_addr = row_addr + self.sm.row_metadata_crc_start;
        let rm_crc = calculate_crc(&rm);
        journal.write_object(rm_crc_addr, &rm_crc, Tracked(perm));
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
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==>
                #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create(*k, item_addr)),
                        used_slots: self@.used_slots,
                        ..old(self)@
                    })
                    &&& self@.used_slots <= old(self)@.used_slots + 1
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

        let row_addr = match self.create_step1(k, item_addr, journal) {
            Ok(r) => r,
            Err(e) => { return Err(e); },
        };
        self.create_step2(k, item_addr, journal, row_addr, Tracked(perm));

        let rm = KeyTableRowMetadata{ item_addr, list_addr: 0 };
        let _ = self.free_list.pop();

        self.memory_mapping = Ghost(self.memory_mapping@.create(row_addr, *k, rm));

        let cki = ConcreteKeyInfo{ row_addr, rm };
        self.m.insert(k.clone_provable(), cki);
        assert(self.m@.remove(*k) =~= old(self).m@);

        let undo_record = KeyUndoRecord::UndoCreate{ row_addr, k: *k };
        assert(self.internal_view().apply_undo_record(undo_record) =~= Some(old(self).internal_view()));
        self.undo_records.push(undo_record);
        assert(self.internal_view().apply_undo_records(self.undo_records@, self.sm) ==
               old(self).internal_view().apply_undo_records(old(self).undo_records@, self.sm)) by {
            assert(self.undo_records@.drop_last() =~= old(self).undo_records@);
            assert(self.undo_records@.last() =~= undo_record);
        }

        self.status = Ghost(KeyTableStatus::Quiescent);

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_validate_row_addr;
        }

        assert(self.valid(journal@));
        assert(self@.tentative =~= Some(old(self)@.tentative.unwrap().create(*k, item_addr)));
        Ok(())
    }

    pub exec fn delete(
        &mut self,
        k: &K,
        row_addr: u64,
        rm: KeyTableRowMetadata,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self)@.tentative.unwrap().key_info[*k] == rm,
            old(self).key_corresponds_to_key_addr(*k, row_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==>
                #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
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
        proof {
            journal.lemma_valid_implications();
            self.lemma_valid_implications(journal@);
            broadcast use pmcopy_axioms;
            broadcast use group_validate_row_addr;
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_update_bytes_effect;
        }

        let cdb_addr = row_addr + self.sm.row_cdb_start;
        let cdb = CDB_FALSE;
        let cdb_bytes = vstd::slice::slice_to_vec(cdb.as_byte_slice());
        match journal.journal_write(cdb_addr, cdb_bytes) {
            Ok(()) => {},
            Err(JournalError::NotEnoughSpace) => {
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            _ => {
                assert(false);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        };

        assert(self.memory_mapping@.valid(self.sm));
        assert(self.memory_mapping == old(self).memory_mapping);
        self.memory_mapping =
            Ghost(self.memory_mapping@.delete(row_addr, *k, rm, self.pending_deallocations@.len()));
        assert(self.memory_mapping@.undo_delete(row_addr, *k, rm) =~= Some(old(self).memory_mapping@));

        self.m.remove(k);
        assert(self.m@.insert(*k, ConcreteKeyInfo{ row_addr, rm }) == old(self).m@);
        self.pending_deallocations.push(row_addr);

        let undo_record = KeyUndoRecord::UndoDelete{ row_addr, k: *k, rm };
        assert(self.internal_view().apply_undo_record(undo_record) =~= Some(old(self).internal_view()));
        self.undo_records.push(undo_record);
        assert(self.internal_view().apply_undo_records(self.undo_records@, self.sm) ==
               old(self).internal_view().apply_undo_records(old(self).undo_records@, self.sm)) by {
            assert(self.undo_records@.drop_last() =~= old(self).undo_records@);
            assert(self.undo_records@.last() =~= undo_record);
        }

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_validate_row_addr;
        }

        assert(self.valid(journal@));
        assert(self@.tentative =~= Some(old(self)@.tentative.unwrap().delete(*k)));
        Ok(())
    }

    #[inline]
    exec fn update_step1(
        &mut self,
        k: &K,
        row_addr: u64,
        new_rm: KeyTableRowMetadata,
        former_rm: KeyTableRowMetadata,
        journal: &mut Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, row_addr),
            old(self)@.tentative.unwrap().key_info[*k] == former_rm,
            ({
                ||| new_rm.item_addr == former_rm.item_addr
                ||| !old(self)@.tentative.unwrap().item_addrs().contains(new_rm.item_addr)
            }),
            ({
                ||| new_rm.list_addr == 0
                ||| new_rm.list_addr == former_rm.list_addr
                ||| !old(self)@.tentative.unwrap().list_addrs().contains(new_rm.list_addr)
            }),
        ensures
            journal.valid(),
            match result {
                Ok(()) => {
                    &&& self == Self{ status: Ghost(KeyTableStatus::Inconsistent), ..*old(self) }
                    &&& self.inv(journal@)
                    &&& self.internal_view().consistent_with_journaled_addrs(journal@.journaled_addrs, self.sm)
                    &&& journal@.matches_except_in_range(old(journal)@, row_addr + self.sm.row_metadata_start,
                                                       row_addr + self.sm.row_metadata_crc_start + u64::spec_size_of())
                    &&& recover_object::<KeyTableRowMetadata>(
                        journal@.commit_state, row_addr + self.sm.row_metadata_start,
                        row_addr + self.sm.row_metadata_crc_start
                    ) == Some(new_rm)
                },
                Err(KvError::OutOfSpace) => {
                    &&& journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int)
                    &&& self.valid(journal@)
                    &&& self@ == KeyTableView { tentative: None, ..old(self)@ }
                },
                _ => false,
            },
    {
        proof {
            journal.lemma_valid_implications();
            self.lemma_valid_implications(journal@);
            broadcast use pmcopy_axioms;
            broadcast use group_validate_row_addr;
            broadcast use group_update_bytes_effect;
        }

        self.status = Ghost(KeyTableStatus::Inconsistent);

        let metadata_addr = row_addr + self.sm.row_metadata_start;
        let rm_bytes = slice_to_vec(new_rm.as_byte_slice());
        match journal.journal_write(metadata_addr, rm_bytes) {
            Ok(()) => {},
            Err(JournalError::NotEnoughSpace) => {
                self.status = Ghost(KeyTableStatus::Quiescent);
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            _ => {
                assert(false);
                self.status = Ghost(KeyTableStatus::Quiescent);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        };

        let rm_crc_addr = row_addr + self.sm.row_metadata_crc_start;
        let rm_crc = calculate_crc(&new_rm);
        let rm_crc_bytes = slice_to_vec(rm_crc.as_byte_slice());
        match journal.journal_write(rm_crc_addr, rm_crc_bytes) {
            Ok(()) => {},
            Err(JournalError::NotEnoughSpace) => {
                self.status = Ghost(KeyTableStatus::Quiescent);
                self.must_abort = Ghost(true);
                return Err(KvError::OutOfSpace);
            },
            _ => {
                assert(false);
                self.status = Ghost(KeyTableStatus::Quiescent);
                self.must_abort = Ghost(true);
                return Err(KvError::InternalError);
            }
        };

        Ok(())
    }

    pub exec fn update(
        &mut self,
        k: &K,
        row_addr: u64,
        new_rm: KeyTableRowMetadata,
        former_rm: KeyTableRowMetadata,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, row_addr),
            old(self)@.tentative.unwrap().key_info[*k] == former_rm,
            ({
                ||| new_rm.item_addr == former_rm.item_addr
                ||| !old(self)@.tentative.unwrap().item_addrs().contains(new_rm.item_addr)
            }),
            ({
                ||| new_rm.list_addr == 0
                ||| new_rm.list_addr == former_rm.list_addr
                ||| !old(self)@.tentative.unwrap().list_addrs().contains(new_rm.list_addr)
            }),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update(*k, new_rm, former_rm)),
                        used_slots: self@.used_slots,
                        ..old(self)@
                    })
                    &&& self@.used_slots <= old(self)@.used_slots + 1
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
        match self.update_step1(k, row_addr, new_rm, former_rm, journal) {
            Ok(()) => {},
            Err(e) => { return Err(e); },
        }

        assert(self.memory_mapping@.valid(self.sm));
        assert(self.memory_mapping == old(self).memory_mapping);
        self.memory_mapping = Ghost(self.memory_mapping@.update(row_addr, *k, new_rm, former_rm));
        assert(self.memory_mapping@.undo_update(row_addr, *k, former_rm) =~= Some(old(self).memory_mapping@));

        self.m.insert(k.clone_provable(), ConcreteKeyInfo{ row_addr, rm: new_rm });
        assert(self.m@.insert(*k, ConcreteKeyInfo{ row_addr, rm: former_rm }) == old(self).m@);

        let undo_record = KeyUndoRecord::UndoUpdate{ row_addr, k: *k, former_rm: former_rm };
        assert(self.internal_view().apply_undo_record(undo_record) =~= Some(old(self).internal_view()));
        self.undo_records.push(undo_record);
        assert(self.internal_view().apply_undo_records(self.undo_records@, self.sm) ==
               old(self).internal_view().apply_undo_records(old(self).undo_records@, self.sm)) by {
            assert(self.undo_records@.drop_last() =~= old(self).undo_records@);
            assert(self.undo_records@.last() =~= undo_record);
        }

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_validate_row_addr;
        }

        self.status = Ghost(KeyTableStatus::Quiescent);

        assert(self.valid(journal@));
        assert(self@.tentative =~= Some(old(self)@.tentative.unwrap().update(*k, new_rm, former_rm)));
        Ok(())
    }

    pub exec fn get_keys(
        &self,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Vec<K>)
        requires
            self.valid(journal@),
            self@.tentative is Some,
        ensures
            result@.to_set() == self@.tentative.unwrap().key_info.dom(),
            result@.no_duplicates(),
    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;

        let keys = self.m.keys();
        let mut result = Vec::<K>::new();
        assert(result@ =~= keys@.1.take(0));

        for k in iter: keys
            invariant
                result@ == iter@,
        {
            assert(iter.keys.take(iter.pos).push(*k) =~= iter.keys.take(iter.pos + 1));
            result.push(*k);
        }

        assert(result@.to_set() =~= self@.tentative.unwrap().key_info.dom()) by {
            assert(keys@.1.to_set() == self.m@.dom());
            assert(keys@.1.take(keys@.1.len() as int) =~= keys@.1);
            assert(self.m@.dom() =~= self@.tentative.unwrap().key_info.dom());
        }

        result
    }
}

}

