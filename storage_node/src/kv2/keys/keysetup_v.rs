#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

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
use super::keys_v::*;
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

pub(super) exec fn exec_setup<PM, K>(
    pm: &mut PM,
    sm: &KeyTableStaticMetadata,
)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
    requires
        old(pm).inv(),
        sm.valid(),
        sm.consistent_with_type::<K>(),
        sm.table.end <= old(pm)@.len(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        recover_keys::<K>(pm@.read_state, *sm) == Some(KeyTableSnapshot::<K>::init()),
        seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
{
    let mut row_index: u64 = 0;
    let mut row_addr: u64 = sm.table.start;
    let cdb_false: u64 = CDB_FALSE;

    proof {
        sm.table.lemma_start_is_valid_row();
    }

    while row_index < sm.table.num_rows
        invariant
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.len() == old(pm)@.len(),
            sm.valid(),
            sm.consistent_with_type::<K>(),
            sm.table.end <= pm@.len(),
            cdb_false == CDB_FALSE,
            0 <= row_index <= sm.table.num_rows,
            sm.table.row_addr_to_index(row_addr as int) == row_index as int,
            row_index < sm.table.num_rows ==> sm.table.validate_row_addr(row_addr as int),
            forall|row_addr: int| {
                &&& #[trigger] sm.table.validate_row_addr(row_addr)
                &&& 0 <= sm.table.row_addr_to_index(row_addr) < row_index
            } ==> recover_cdb(pm@.read_state, row_addr + sm.row_cdb_start) == Some(false),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        proof {
            broadcast use group_validate_row_addr;
            broadcast use group_update_bytes_effect;
            broadcast use pmcopy_axioms;
            sm.table.lemma_row_addr_successor_is_valid(row_addr as int);
        }

        let cdb_addr = row_addr + sm.row_cdb_start;
        pm.serialize_and_write::<u64>(cdb_addr, &cdb_false);
        assert(recover_cdb(pm@.read_state, row_addr + sm.row_cdb_start) == Some(false));

        row_index = row_index + 1;
        row_addr = row_addr + sm.table.row_size;
    }

    assert forall|row_addr: int| #[trigger] sm.table.validate_row_addr(row_addr)
        implies recover_cdb(pm@.read_state, row_addr + sm.row_cdb_start) == Some(false) by {
        let row_index = sm.table.row_addr_to_index(row_addr);
        broadcast use group_validate_row_addr;
    }

    let ghost mapping = KeyRecoveryMapping::<K>::new_empty(sm.table);
    assert(KeyRecoveryMapping::<K>::new(pm@.read_state, *sm) == Some(mapping)) by {
        assert(mapping.corresponds(pm@.read_state, *sm));
        mapping.lemma_corresponds_implies_equals_new(pm@.read_state, *sm);
    }
    assert(recover_keys_from_mapping::<K>(mapping) =~= KeyTableSnapshot::<K>::init());
}

}
