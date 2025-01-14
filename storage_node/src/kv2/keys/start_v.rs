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

verus! {

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
            journal@.valid(),
            journal@.journaled_addrs.is_empty(),
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
        let ghost m = KeyRecoveryMapping::<K>::new(journal@.read_state, *sm).unwrap();
        assert(m.corresponds(journal@.read_state, *sm));

        let ghost mut memory_mapping = KeyMemoryMapping::<K>::new(*sm);
        
        let mut row_index: u64 = 0;
        let mut row_addr: u64 = sm.table.start;
        let pm = journal.get_pm_region_ref();
    
        proof {
            sm.table.lemma_start_is_valid_row();
        }

        while row_index < sm.table.num_rows
            invariant
                journal.valid(),
                journal@.valid(),
                journal@.journaled_addrs.is_empty(),
                journal@.durable_state == journal@.read_state,
                journal@.read_state == journal@.commit_state,
                Self::recover(journal@.read_state, *sm) is Some,
                sm.valid::<K>(),
                sm.end() <= journal@.durable_state.len(),
                vstd::std_specs::hash::obeys_key_model::<K>(),
                m.corresponds(journal@.read_state, *sm),
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
                memory_mapping.consistent(),
        /*
                forall|any_row_addr: u64| {
                    &&& #[trigger] sm.table.validate_row_addr(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                } ==> recover_cdb(pm@.read_state, any_row_addr + sm.row_cdb_start) == Some(false),
        */
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use group_update_bytes_effect;
                broadcast use pmcopy_axioms;
                sm.table.lemma_row_addr_successor_is_valid(row_addr);
                assert(sm.table.validate_row_addr(row_addr));
                assert(m.row_info.contains_key(row_addr));
            }
    
            let cdb_addr = row_addr + sm.row_cdb_start;
            let cdb = exec_recover_cdb::<PM>(pm, cdb_addr);
            if cdb.is_none() {
                return Err(KvError::CRCMismatch);
            }
    
            row_index = row_index + 1;
            row_addr = row_addr + sm.table.row_size;
        }
        
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

