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
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

broadcast use group_hash_axioms;

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start(
        journal: &Journal<TrustedKvPermission, PM>,
        sm: &KeyTableStaticMetadata,
    ) -> (result: Result<(Self, HashSet<u64>, HashSet<u64>), KvError<K>>)
        requires
            journal.valid(),
            journal.recover_idempotent(),
            journal@.valid(),
            journal@.journaled_addrs == Set::<int>::empty(),
            journal@.durable_state == journal@.read_state,
            journal@.read_state == journal@.commit_state,
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
                    &&& item_addrs@ == recovered_state.item_addrs()
                    &&& list_addrs@ == recovered_state.list_addrs()
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            }
    {
        let ghost recovery_mapping = KeyRecoveryMapping::<K>::new(journal@.read_state, *sm).unwrap();
        assert(recovery_mapping.corresponds(journal@.read_state, *sm));

        let ghost mut memory_mapping = KeyMemoryMapping::<K>::new(*sm);
        
        let mut row_index: u64 = 0;
        let mut row_addr: u64 = sm.table.start;
        let pm = journal.get_pm_region_ref();
        let mut free_list = Vec::<u64>::new();
        let mut m = HashMap::<K, ConcreteKeyInfo>::new();
        let mut item_addrs = HashSet::<u64>::new();
        let mut list_addrs = HashSet::<u64>::new();
    
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
                Self::recover(journal@.read_state, *sm) is Some,
                sm.valid::<K>(),
                sm.end() <= journal@.durable_state.len(),
                vstd::std_specs::hash::obeys_key_model::<K>(),
                KeyRecoveryMapping::<K>::new(journal@.read_state, *sm) == Some(recovery_mapping),
                pm.inv(),
                pm.constants() == journal@.pm_constants,
                pm@.valid(),
                pm@.read_state == journal@.read_state,
                sm.valid::<K>(),
                sm.table.end <= pm@.len(),
                0 <= row_index <= sm.table.num_rows,
                sm.table.row_addr_to_index(row_addr) == row_index as int,
                sm.table.start <= row_addr <= sm.table.end,
                row_index < sm.table.num_rows ==> sm.table.validate_row_addr(row_addr),
                forall|any_row_addr: u64|
                    #![trigger sm.table.validate_row_addr(any_row_addr)]
                    #![trigger memory_mapping.row_info.contains_key(any_row_addr)]
                {
                    &&& sm.table.validate_row_addr(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                } ==> {
                    &&& memory_mapping.row_info.contains_key(any_row_addr)
                    &&& memory_mapping.corresponds_to_snapshot_at_addr(recovery_mapping, any_row_addr)
                },
                forall|any_row_addr: u64| #[trigger] memory_mapping.row_info.contains_key(any_row_addr) ==>
                    0 <= sm.table.row_addr_to_index(any_row_addr) < row_index,
                memory_mapping.sm == sm,
                memory_mapping.consistent(),
                memory_mapping.consistent_with_state(journal@.read_state),
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
                    memory_mapping = memory_mapping.update(row_addr, k, rm);
                }
                let concrete_key_info = ConcreteKeyInfo{ row_addr, rm };
                m.insert(k, concrete_key_info);
                item_addrs.insert(rm.item_addr);
                if rm.list_addr != 0 {
                    list_addrs.insert(rm.list_addr);
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
            phantom: Ghost(None),
        };

        let ghost recovered_state = Self::recover(journal@.read_state, *sm).unwrap();
        assert(keys@.durable =~= recovered_state);
        assert(item_addrs@ =~= recovered_state.item_addrs());
        assert(list_addrs@.insert(0) =~= keys@.durable.list_addrs());
        list_addrs.insert(0);

        Ok((keys, item_addrs, list_addrs))
    }
}

}

