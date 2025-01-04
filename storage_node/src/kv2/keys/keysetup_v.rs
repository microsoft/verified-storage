#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
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
use super::keys_v::*;
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

pub(super) open spec fn spec_space_needed_for_key_table_setup<K>(ps: SetupParameters) -> int
    where
        K: PmCopy,
    recommends
        ps.valid(),
{
    let row_metadata_start = u64::spec_size_of();
    let row_metadata_end = row_metadata_start + KeyTableRowMetadata::spec_size_of();
    let row_metadata_crc_start = row_metadata_end;
    let row_metadata_crc_end = row_metadata_crc_start + u64::spec_size_of();
    let row_key_start = row_metadata_crc_end;
    let row_key_end = row_key_start + K::spec_size_of();
    let row_key_crc_start = row_key_end;
    let row_key_crc_end = row_key_crc_start + u64::spec_size_of();
    let row_size = row_key_crc_end;
    let num_rows = ps.num_keys;
    opaque_mul(num_rows as int, row_size as int)
}

pub(super) exec fn get_space_needed_for_key_table_setup<K>(ps: &SetupParameters) -> (result: OverflowingU64)
    where
        K: PmCopy,
    requires
        ps.valid(),
    ensures
        result@ == spec_space_needed_for_key_table_setup::<K>(*ps),
{
    broadcast use pmcopy_axioms;

    let row_cdb_start = OverflowingU64::new(0);
    let row_metadata_start = row_cdb_start.add_usize(size_of::<u64>());
    let row_metadata_end = row_metadata_start.add_usize(size_of::<KeyTableRowMetadata>());
    let row_metadata_crc_end = row_metadata_end.add_usize(size_of::<u64>());
    let row_key_end = row_metadata_crc_end.add_usize(size_of::<K>());
    let row_key_crc_end = row_key_end.add_usize(size_of::<u64>());
    let num_rows = OverflowingU64::new(ps.num_keys);
    num_rows.mul_overflowing_u64(&row_key_crc_end)
}

pub(super) exec fn exec_setup_given_metadata<PM, K>(
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

pub(super) exec fn exec_setup<PM, K>(
    pm: &mut PM,
    ps: &SetupParameters,
    start: u64,
    max_end: u64,
) -> (result: Result<KeyTableStaticMetadata, KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
    requires
        old(pm).inv(),
        ps.valid(),
        start <= max_end <= old(pm)@.len(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        match result {
            Ok(sm) => {
                &&& recover_keys::<K>(pm@.read_state, sm) == Some(KeyTableSnapshot::<K>::init())
                &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int,
                                             sm.table.end as int)
                &&& sm.valid()
                &&& sm.consistent_with_type::<K>()
                &&& sm.table.start == start
                &&& sm.table.end <= max_end
                &&& sm.table.end - sm.table.start <= spec_space_needed_for_key_table_setup::<K>(*ps)
                &&& sm.table.num_rows == ps.num_keys
            },
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(KvError::OutOfSpace) => {
                &&& pm@ == old(pm)@
                &&& max_end - start < spec_space_needed_for_key_table_setup::<K>(*ps)
            },
            _ => false,
        }
{
    broadcast use pmcopy_axioms;

    let key_size = size_of::<K>();
    if key_size == 0 {
        return Err(KvError::KeySizeTooSmall);
    }

    let row_cdb_start = OverflowingU64::new(0);
    let row_metadata_start = row_cdb_start.add_usize(size_of::<u64>());
    let row_metadata_end = row_metadata_start.add_usize(size_of::<KeyTableRowMetadata>());
    let row_metadata_crc_end = row_metadata_end.add_usize(size_of::<u64>());
    let row_key_end = row_metadata_crc_end.add_usize(key_size);
    let row_key_crc_end = row_key_end.add_usize(size_of::<u64>());
    let num_rows = ps.num_keys;
    let space_required = OverflowingU64::new(num_rows).mul_overflowing_u64(&row_key_crc_end);

    assert(space_required@ == spec_space_needed_for_key_table_setup::<K>(*ps));
    assert(space_required@ >= row_key_crc_end@) by {
        reveal(opaque_mul);
        vstd::arithmetic::mul::lemma_mul_ordering(num_rows as int, row_key_crc_end@);
    }

    if space_required.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }

    let space_required = space_required.unwrap();
    if space_required > max_end - start {
        return Err(KvError::OutOfSpace);
    }

    let table = TableMetadata::new(
        start,
        start + space_required,
        num_rows,
        row_key_crc_end.unwrap(),
    );
    let sm = KeyTableStaticMetadata {
        table,
        key_size: key_size as u64,
        row_cdb_start: 0,
        row_metadata_start: row_metadata_start.unwrap(),
        row_metadata_end: row_metadata_end.unwrap(),
        row_metadata_crc_start: row_metadata_end.unwrap(),
        row_key_start: row_metadata_crc_end.unwrap(),
        row_key_end: row_key_end.unwrap(),
        row_key_crc_start: row_key_end.unwrap(),
    };

    exec_setup_given_metadata::<PM, K>(pm, &sm);
    Ok(sm)
}

}
