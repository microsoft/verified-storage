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
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn space_needed_for_setup(ps: &SetupParameters, min_start: &OverflowingU64)
                                       -> (result: OverflowingU64)
        ensures
            result@ == Self::spec_space_needed_for_setup(*ps, min_start@),
    {
        broadcast use pmcopy_axioms;
    
        let row_metadata_start = OverflowingU64::new(size_of::<u64>() as u64);
        let row_metadata_end = row_metadata_start.add_usize(size_of::<KeyTableRowMetadata>());
        let row_metadata_crc_end = row_metadata_end.add_usize(size_of::<u64>());
        let row_key_end = row_metadata_crc_end.add_usize(size_of::<K>());
        let row_key_crc_end = row_key_end.add_usize(size_of::<u64>());
        let num_rows = OverflowingU64::new(ps.num_keys);
        let table_size = num_rows.mul_overflowing_u64(&row_key_crc_end);
        let initial_space: u64 = if min_start.is_overflowed() {
            0u64
        } else {
            get_space_needed_for_alignment_usize(min_start.unwrap(), size_of::<u64>()) as u64
        };
        OverflowingU64::new(initial_space).add_overflowing_u64(&table_size)
    }

    exec fn setup_given_metadata(
        pm: &mut PM,
        sm: &KeyTableStaticMetadata,
    )
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            sm.valid::<K>(),
            sm.table.end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            Self::recover_keys(pm@.read_state, *sm) == Some(KeyTableSnapshot::<K>::init()),
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
                pm@.valid(),
                pm@.len() == old(pm)@.len(),
                sm.valid::<K>(),
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
        assert(Self::recover_keys_from_mapping(mapping) =~= KeyTableSnapshot::<K>::init());
    }
    
    pub exec fn setup(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<KeyTableStaticMetadata, KvError<K>>)
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, sm) == Some(KeyTableSnapshot::<K>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.start() as int,
                                                 sm.end() as int)
                    &&& sm.valid::<K>()
                    &&& min_start <= sm.start() <= sm.end() <= max_end
                    &&& sm.end() - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat)
                    &&& sm.num_rows() == ps.num_keys
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) =>
                    max_end - min_start < Self::spec_space_needed_for_setup(*ps, min_start as nat),
                _ => false,
            }
    {
        let key_size = size_of::<K>();
        if key_size == 0 {
            broadcast use axiom_bytes_len;
            return Err(KvError::KeySizeTooSmall);
        }
    
        let row_cdb_start = OverflowingU64::new(0);
        let row_metadata_start = row_cdb_start.add_usize(size_of::<u64>());
        let row_metadata_end = row_metadata_start.add_usize(size_of::<KeyTableRowMetadata>());
        let row_metadata_crc_end = row_metadata_end.add_usize(size_of::<u64>());
        let row_key_end = row_metadata_crc_end.add_usize(key_size);
        let row_key_crc_end = row_key_end.add_usize(size_of::<u64>());
        let start = OverflowingU64::new(min_start).align(size_of::<u64>());
        let num_rows = ps.num_keys;
        let space_required = OverflowingU64::new(num_rows).mul_overflowing_u64(&row_key_crc_end);
        let end = start.add_overflowing_u64(&space_required);
    
        assert(end@ - min_start@ == Self::spec_space_needed_for_setup(*ps, min_start as nat));
        assert(space_required@ >= row_key_crc_end@) by {
            vstd::arithmetic::mul::lemma_mul_ordering(num_rows as int, row_key_crc_end@ as int);
        }
    
        if end.is_overflowed() {
            return Err(KvError::OutOfSpace);
        }
    
        if end.unwrap() > max_end {
            return Err(KvError::OutOfSpace);
        }
    
        let table = TableMetadata::new(
            start.unwrap(),
            end.unwrap(),
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
    
        Self::setup_given_metadata(pm, &sm);
        Ok(sm)
    }
}

}

