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
use super::items_v::*;
use super::itemrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

pub(super) open spec fn local_spec_space_needed_for_setup<I>(ps: SetupParameters, min_start: nat) -> nat
    where
        I: PmCopy,
    recommends
        ps.valid(),
{
    // let row_item_start = 0;
    let row_item_end = I::spec_size_of();
    let row_item_crc_end = row_item_end + u64::spec_size_of();
    let row_size = row_item_crc_end;
    let num_rows = ps.num_keys;
    let table_size = num_rows as int * row_size;
    let initial_space = if min_start > u64::MAX { 0 } else {
        space_needed_for_alignment(min_start as int, u64::spec_size_of() as int)
    };
    (initial_space + table_size) as nat
}

pub(super) exec fn local_space_needed_for_setup<I>(ps: &SetupParameters, min_start: &OverflowingU64)
                                                   -> (result: OverflowingU64)
    where
        I: PmCopy,
    requires
        ps.valid(),
    ensures
        result@ == local_spec_space_needed_for_setup::<I>(*ps, min_start@),
{
    broadcast use pmcopy_axioms;

    let row_item_end = OverflowingU64::new(size_of::<I>() as u64);
    let row_item_crc_end = row_item_end.add_usize(size_of::<u64>());
    let num_rows = OverflowingU64::new(ps.num_keys);
    let table_size = num_rows.mul_overflowing_u64(&row_item_crc_end);
    let initial_space = if min_start.is_overflowed() { 0 } else {
        get_space_needed_for_alignment_usize(min_start.unwrap(), size_of::<u64>()) as u64
    };
    OverflowingU64::new(initial_space).add_overflowing_u64(&table_size)
}

pub(super) exec fn exec_setup_given_metadata<PM, I>(
    pm: &mut PM,
    sm: &ItemTableStaticMetadata,
)
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
    requires
        old(pm).inv(),
        old(pm)@.valid(),
        sm.valid(),
        sm.consistent_with_type::<I>(),
        sm.table.end <= old(pm)@.len(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        pm@.valid(),
        pm@.len() == old(pm)@.len(),
        local_recover::<I>(pm@.read_state, Set::<u64>::empty(), *sm) == Some(ItemTableSnapshot::<I>::init()),
        seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
{
    assert(local_recover::<I>(pm@.read_state, Set::<u64>::empty(), *sm) =~= Some(ItemTableSnapshot::<I>::init()));
}

pub(super) exec fn local_setup<PM, I, K>(
    pm: &mut PM,
    ps: &SetupParameters,
    min_start: u64,
    max_end: u64,
) -> (result: Result<ItemTableStaticMetadata, KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
        K: std::fmt::Debug,
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
                &&& local_recover::<I>(pm@.read_state, Set::<u64>::empty(), sm) == Some(ItemTableSnapshot::<I>::init())
                &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int,
                                              sm.table.end as int)
                &&& sm.valid()
                &&& sm.consistent_with_type::<I>()
                &&& min_start <= sm.table.start <= sm.table.end <= max_end
                &&& sm.table.end - min_start == local_spec_space_needed_for_setup::<I>(*ps, min_start as nat)
                &&& sm.table.num_rows == ps.num_keys
            },
            Err(KvError::OutOfSpace) =>
                max_end - min_start < local_spec_space_needed_for_setup::<I>(*ps, min_start as nat),
            _ => false,
        }
{
    broadcast use pmcopy_axioms;

    let item_size = size_of::<I>();
    assert(item_size == I::spec_size_of()) by {
        broadcast use pmcopy_axioms;
    }

    let row_item_end = OverflowingU64::new(size_of::<I>() as u64);
    let row_item_crc_end = row_item_end.add_usize(size_of::<u64>());
    let num_rows = OverflowingU64::new(ps.num_keys);
    let start = OverflowingU64::new(min_start).align(size_of::<u64>());
    let table_size = num_rows.mul_overflowing_u64(&row_item_crc_end);
    let end = start.add_overflowing_u64(&table_size);

    assert(end@ - min_start == local_spec_space_needed_for_setup::<I>(*ps, min_start as nat));
    assert(table_size@ >= row_item_crc_end@) by {
        vstd::arithmetic::mul::lemma_mul_ordering(ps.num_keys as int, row_item_crc_end@ as int);
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
        ps.num_keys,
        row_item_crc_end.unwrap(),
    );
    let sm = ItemTableStaticMetadata {
        table,
        item_size: item_size as u64,
        row_item_start: 0,
        row_item_end: row_item_end.unwrap(),
        row_item_crc_start: row_item_end.unwrap(),
    };

    exec_setup_given_metadata::<PM, I>(pm, &sm);
    Ok(sm)
}

}
