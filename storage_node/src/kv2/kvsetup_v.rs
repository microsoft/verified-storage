#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::keys::*;
use super::items::*;
use super::kvimpl_t::*;
use super::kvrecover_v::*;
use super::kvspec_t::*;
use super::lists::*;

verus! {

pub(super) open spec fn spec_space_needed_for_setup<PM, K, I, L>(ps: SetupParameters) -> nat
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    recommends
        ps.valid(),
{
    let key_table_size = KeyTable::<PM, K>::space_needed_for_setup(ps);
    let item_table_size = ItemTable::<PM, I>::space_needed_for_setup(ps);
    let list_table_size = ListTable::<PM, L>::space_needed_for_setup(ps);
    let app_area_size = (key_table_size + item_table_size + list_table_size) as nat;
    if app_area_size > u64::MAX {
        app_area_size
    }
    else {
        let max_journal_entries = (ps.max_operations_per_transaction
                                   + ps.max_operations_per_transaction
                                   + ps.max_operations_per_transaction
                                   + ps.max_operations_per_transaction) as nat;
        if max_journal_entries > u64::MAX {
            max_journal_entries
        }
        else {
            let jsp = JournalSetupParameters {
                app_version_number: KVSTORE_PROGRAM_VERSION_NUMBER,
                app_program_guid: KVSTORE_PROGRAM_GUID,
                max_journal_entries: max_journal_entries as u64,
                max_journaled_bytes: ps.max_data_bytes_per_transaction,
                app_area_size: app_area_size as u64,
                app_area_alignment: 256,
            };
            Journal::<TrustedKvPermission, PM>::space_needed_for_setup(jsp)
        }
    }
}

exec fn exec_check_setup_parameters(ps: &SetupParameters) -> (result: bool)
    ensures
        result == ps.valid(),
{
    if ps.num_keys == 0 { false }
    else if ps.num_list_entries_per_block == 0 { false }
    else if ps.num_list_blocks == 0 { false }
    else if ps.num_lists_to_cache == 0 { false }
    else if ps.max_operations_per_transaction == 0 { false }
    else if ps.max_data_bytes_per_transaction == 0 { false }
    else { true }
}

pub(super) exec fn exec_get_space_needed_for_setup<PM, K, I, L>(ps: &SetupParameters)
                                                                -> (result: Result<u64, KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    ensures
        match result {
            Ok(v) => v == spec_space_needed_for_setup::<PM, K, I, L>(*ps),
            Err(KvError::InvalidParameter) => !ps.valid(),
            Err(KvError::OutOfSpace) => spec_space_needed_for_setup::<PM, K, I, L>(*ps) > u64::MAX,
            Err(_) => false,
        },
{
    if !exec_check_setup_parameters(ps) {
        return Err(KvError::InvalidParameter);
    }

    let key_table_size = KeyTable::<PM, K>::get_space_needed_for_setup(ps);
    let item_table_size = ItemTable::<PM, I>::get_space_needed_for_setup(ps);
    let list_table_size = ListTable::<PM, L>::get_space_needed_for_setup(ps);
    let app_area_size = key_table_size.add_overflowing_u64(&item_table_size).add_overflowing_u64(&list_table_size);
    if app_area_size.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }

    let max_journal_entries = OverflowingU64::new(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction);
    if max_journal_entries.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }

    let jsp = JournalSetupParameters {
        app_version_number: KVSTORE_PROGRAM_VERSION_NUMBER,
        app_program_guid: KVSTORE_PROGRAM_GUID,
        max_journal_entries: max_journal_entries.unwrap(),
        max_journaled_bytes: ps.max_data_bytes_per_transaction,
        app_area_size: app_area_size.unwrap(),
        app_area_alignment: 256,
    };
    match Journal::<TrustedKvPermission, PM>::get_space_needed_for_setup(&jsp) {
        None => Err(KvError::OutOfSpace),
        Some(v) => Ok(v),
    }
}

pub(super) exec fn setup_kv<PM, K, I, L>(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires 
        old(pm).inv(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        match result {
            Ok(()) => {
                &&& pm@.flush_predicted()
                &&& recover_journal_then_kv::<PM, K, I, L>(pm@.durable_state)
                    == Some(AtomicKvStore::<K, I, L>::init(ps.kvstore_id, ps.logical_range_gaps_policy))
            },
            Err(KvError::InvalidParameter) => {
                &&& pm@ == old(pm)@
                &&& !ps.valid()
            },
            Err(KvError::KeySizeTooSmall) => {
                &&& pm@ == old(pm)@
                &&& K::spec_size_of() == 0
            },
            Err(KvError::OutOfSpace) => pm@.len() < spec_space_needed_for_setup::<PM, K, I, L>(*ps),
            Err(_) => false,
        },
{
    if !exec_check_setup_parameters(ps) {
        return Err(KvError::InvalidParameter);
    }

    proof {
        pm.lemma_inv_implies_view_valid();
    }

    let pm_size = pm.get_region_size();

    let key_table_size = KeyTable::<PM, K>::get_space_needed_for_setup(ps);
    let item_table_size = ItemTable::<PM, I>::get_space_needed_for_setup(ps);
    let list_table_size = ListTable::<PM, L>::get_space_needed_for_setup(ps);
    let app_area_size = key_table_size.add_overflowing_u64(&item_table_size).add_overflowing_u64(&list_table_size);
    if app_area_size.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }

    let max_journal_entries = OverflowingU64::new(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction)
                                  .add(ps.max_operations_per_transaction);
    if max_journal_entries.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }

    let jsp = JournalSetupParameters {
        app_version_number: KVSTORE_PROGRAM_VERSION_NUMBER,
        app_program_guid: KVSTORE_PROGRAM_GUID,
        max_journal_entries: max_journal_entries.unwrap(),
        max_journaled_bytes: ps.max_data_bytes_per_transaction,
        app_area_size: app_area_size.unwrap(),
        app_area_alignment: 256,
    };

    let key_size = size_of::<K>();
    assert(key_size == K::spec_size_of()) by {
        broadcast use pmcopy_axioms;
    }
    if key_size == 0 {
        return Err(KvError::KeySizeTooSmall);
    }

    let jc = match Journal::<TrustedKvPermission, PM>::begin_setup(pm, &jsp) {
        Ok(jc) => jc,
        Err(JournalError::InvalidAlignment) => { assert(false); return Err(KvError::OutOfSpace); },
        Err(JournalError::NotEnoughSpace) => { return Err(KvError::OutOfSpace); },
        Err(_) => { assert(false); return Err(KvError::OutOfSpace); },
    };

    /*
    let key_sm = match KeyTable::<PM, K>::setup(pm, ps, jc.app_area_start, jc.app_area_end) {
        Ok(key_sm) => key_sm,
        Err(e) => return Err(e),
    };
    let item_sm = ItemTable::<PM, I>::setup::<K>(pm, ps, key_sm.table.end, jc.app_area_end);
    */

    assume(false);
    Ok(())
}

}

