#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::journal::Journal;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use super::impl_v::*;
use super::inv_v::*;
use super::recover_v::*;
use super::spec_v::*;
use super::super::spec_t::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {

broadcast use group_hash_axioms;
impl<PM, K> KeyTable<PM, K>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start(
        journal: &Journal<PM>,
        sm: &KeyTableStaticMetadata,
    ) -> (result: Result<(Self, HashSet<u64>, Vec<u64>), KvError>)
        requires
            journal.valid(),
            journal.recover_idempotent(),
            journal@.valid(),
            journal@.journaled_addrs == Set::<int>::empty(),
            journal@.durable_state == journal@.read_state,
            journal@.read_state == journal@.commit_state,
            journal@.constants.app_area_start <= sm.start(),
            sm.end() <= journal@.constants.app_area_end,
            Self::recover(journal@.read_state, *sm) is Some,
            sm.valid::<K>(),
            sm.end() <= journal@.durable_state.len(),
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
            match result {
                Ok((keys, item_addrs, list_addrs)) => {
                    let recovered_state = Self::recover(journal@.read_state, *sm).unwrap();
                    &&& keys.valid(journal@)
                    &&& keys@.sm == *sm
                    &&& keys@.durable == recovered_state
                    &&& keys@.tentative == Some(recovered_state)
                    &&& recovered_state.key_info.dom().finite()
                    &&& keys@.used_slots == recovered_state.key_info.dom().len()
                    &&& item_addrs@ == recovered_state.item_addrs()
                    &&& list_addrs@.to_set() == recovered_state.list_addrs()
                    &&& !list_addrs@.contains(0)
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            }
    {
        let ghost recovery_mapping = KeyRecoveryMapping::<K>::new(journal@.read_state, *sm).unwrap();
        assert(recovery_mapping.corresponds(journal@.read_state, *sm));

        let mut m = HashMap::<K, ConcreteKeyInfo>::new();
        let mut free_list = Vec::<u64>::new();
        let ghost mut memory_mapping = KeyMemoryMapping::<K>::new();
        let mut item_addrs = HashSet::<u64>::new();
        let mut list_addrs = Vec::<u64>::new();

        let pm = journal.get_pm_region_ref();
        let mut row_index: u64 = 0;
        let mut row_addr: u64 = sm.table.start;
    
        proof {
            sm.table.lemma_start_is_valid_row();
        }

        while row_index < sm.table.num_rows
            invariant
                journal.valid(),
                journal.recover_idempotent(),
                journal@.valid(),
                journal@.journaled_addrs == Set::<int>::empty(),
                journal@.durable_state == journal@.read_state,
                journal@.read_state == journal@.commit_state,
                journal@.constants.app_area_start <= sm.start(),
                sm.end() <= journal@.constants.app_area_end,
                Self::recover(journal@.read_state, *sm) is Some,
                sm.valid::<K>(),
                sm.end() <= journal@.durable_state.len(),
                vstd::std_specs::hash::obeys_key_model::<K>(),
                KeyRecoveryMapping::<K>::new(journal@.read_state, *sm) == Some(recovery_mapping),
                pm.inv(),
                pm.constants() == journal@.pm_constants,
                pm@.valid(),
                pm@.read_state == journal@.read_state,
                sm.table.end <= pm@.len(),
                0 <= row_index <= sm.table.num_rows,
                sm.table.row_addr_to_index(row_addr) == row_index as int,
                sm.table.start <= row_addr <= sm.table.end,
                row_index < sm.table.num_rows ==> sm.table.validate_row_addr(row_addr),
                forall|any_row_addr: u64| {
                    &&& #[trigger] sm.table.validate_row_addr(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                } ==> {
                    &&& memory_mapping.row_info.contains_key(any_row_addr)
                    &&& memory_mapping.corresponds_to_snapshot_at_addr(recovery_mapping, any_row_addr)
                },
                forall|any_row_addr: u64| #[trigger] memory_mapping.row_info.contains_key(any_row_addr) ==>
                    0 <= sm.table.row_addr_to_index(any_row_addr) < row_index,
                memory_mapping.consistent(*sm),
                memory_mapping.consistent_with_state(journal@.read_state, *sm),
                memory_mapping.consistent_with_free_list_and_pending_deallocations(free_list@, Seq::<u64>::empty()),
                memory_mapping.consistent_with_hash_table(m@),
                forall|i: int| #![trigger free_list@[i]] 0 <= i < free_list@.len() ==> {
                    let free_row_addr = free_list@[i];
                    &&& sm.table.validate_row_addr(free_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(free_row_addr) < row_index
                },
                forall|k: K| #[trigger] m@.contains_key(k) ==> {
                    let used_row_addr = m@[k].row_addr;
                    &&& sm.table.validate_row_addr(used_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(used_row_addr) < row_index
                    &&& memory_mapping.row_info.contains_key(used_row_addr)
                    &&& memory_mapping.row_info[used_row_addr] is InHashTable
                },
                !memory_mapping.list_info.contains_key(0),
                forall|any_row_addr: u64| {
                    &&& #[trigger] recovery_mapping.row_info.contains_key(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                    &&& recovery_mapping.row_info[any_row_addr] is Some
                } ==> {
                    let (_, rm) = recovery_mapping.row_info[any_row_addr].unwrap();
                    &&& item_addrs@.contains(rm.item_addr)
                    &&& rm.list_addr != 0 ==> list_addrs@.contains(rm.list_addr)
                },
                forall|item_addr: u64| #[trigger] item_addrs@.contains(item_addr) ==>
                    recovery_mapping.item_info.contains_key(item_addr),
                forall|list_addr: u64| #[trigger] list_addrs@.contains(list_addr) ==>
                    recovery_mapping.list_info.contains_key(list_addr),
                !list_addrs@.contains(0),
            decreases
                sm.table.num_rows - row_index,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use group_update_bytes_effect;
                broadcast use pmcopy_axioms;
                sm.table.lemma_row_addr_successor_is_valid(row_addr);
            }
    
            let cdb_addr = row_addr + sm.row_cdb_start;
            let cdb = exec_recover_cdb::<PM>(pm, cdb_addr);
            if cdb.is_none() {
                return Err(KvError::CRCMismatch);
            }
            let cdb = cdb.unwrap();

            let ghost old_memory_mapping = memory_mapping;
            let ghost old_m = m@;
            let ghost old_list_addrs = list_addrs@;

            if cdb {
                let key_addr = row_addr + sm.row_key_start;
                let key_crc_addr = row_addr + sm.row_key_crc_start;
                let k = match exec_recover_object::<PM, K>(pm, key_addr, key_crc_addr) {
                    None => { return Err(KvError::CRCMismatch); },
                    Some(k) => k,
                };
                let rm_addr = row_addr + sm.row_metadata_start;
                let rm_crc_addr = row_addr + sm.row_metadata_crc_start;
                let rm = match exec_recover_object::<PM, KeyTableRowMetadata>(pm, rm_addr, rm_crc_addr) {
                    None => { return Err(KvError::CRCMismatch); },
                    Some(r) => r,
                };
                proof {
                    memory_mapping = memory_mapping.initialize_row(row_addr, k, rm);
                }
                let concrete_key_info = ConcreteKeyInfo{ row_addr, rm };
                m.insert(k, concrete_key_info);
                item_addrs.insert(rm.item_addr);
                if rm.list_addr != 0 {
                    list_addrs.push(rm.list_addr);
                    // Make any trigger about the new list trigger a fact about the old list.
                    assert(forall|list_addr: u64| #[trigger] list_addrs@.contains(list_addr) ==>
                           old_list_addrs.contains(list_addr) || list_addr == rm.list_addr);
                    assert forall|list_addr: u64| #[trigger] old_list_addrs.contains(list_addr) implies
                           list_addrs@.contains(list_addr) by {
                        let i = choose|i: int| 0 <= i < old_list_addrs.len() && #[trigger] old_list_addrs[i] == list_addr;
                        assert(list_addrs@[i] == old_list_addrs[i]);
                    }
                    assert(list_addrs@[list_addrs@.len() - 1] == rm.list_addr);
                }
            }
            else {
                proof {
                    memory_mapping = memory_mapping.mark_in_free_list(row_addr, free_list.len() as nat);
                }
                free_list.push(row_addr);
            }

            row_index = row_index + 1;
            row_addr = row_addr + sm.table.row_size;
        }
    
        assert forall|row_addr: u64| #[trigger] sm.table.validate_row_addr(row_addr)
            implies memory_mapping.row_info.contains_key(row_addr) by {
            let row_index = sm.table.row_addr_to_index(row_addr);
            broadcast use group_validate_row_addr;
        }

        let keys = Self{
            status: Ghost(KeyTableStatus::Quiescent),
            must_abort: Ghost(false),
            sm: sm.clone(),
            m,
            free_list,
            pending_deallocations: Vec::<u64>::new(),
            memory_mapping: Ghost(memory_mapping),
            undo_records: Vec::<KeyUndoRecord<K>>::new(),
            phantom_pm: Ghost(core::marker::PhantomData),
        };

        let ghost recovered_state = Self::recover(journal@.read_state, *sm).unwrap();
        assert(keys@.durable =~= recovered_state);
        assert(item_addrs@ =~= recovered_state.item_addrs());
        assert(list_addrs@.to_set() =~= recovered_state.list_addrs());

        proof {
            memory_mapping.lemma_corresponds_implication_for_free_list_length(free_list@, *sm);
        }

        Ok((keys, item_addrs, list_addrs))
    }
}

}

