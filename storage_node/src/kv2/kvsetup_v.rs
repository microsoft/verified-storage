#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::nonlinear_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
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

exec fn exec_check_setup_parameters(ps: &SetupParameters) -> (result: bool)
    ensures
        result == ps.valid(),
{
    if ps.num_keys == 0 { false }
    else if ps.num_list_entries_per_block == 0 { false }
    else if ps.num_list_blocks == 0 { false }
    else if ps.num_lists_to_cache == 0 { false }
    else if ps.max_operations_per_transaction == 0 { false }
    else { true }
}

pub(super) open spec fn spec_space_needed_for_journal_capacity<PM, K, I, L>(ps: SetupParameters) -> nat
    where
        PM: PersistentMemoryRegion,
        L: PmCopy,
{
    let bytes_per_operation =
        Journal::<TrustedKvPermission, PM>::spec_journal_entry_overhead() * 4
        + L::spec_size_of()
        + u64::spec_size_of() * 8;
    opaque_mul(ps.max_operations_per_transaction as int, bytes_per_operation as int) as nat
}

pub(super) exec fn space_needed_for_journal_capacity<PM, K, I, L>(ps: &SetupParameters) -> (result: OverflowingU64)
    where
        PM: PersistentMemoryRegion,
        L: PmCopy,
    ensures
        result@ == spec_space_needed_for_journal_capacity::<PM, K, I, L>(*ps),
{
    broadcast use pmcopy_axioms;
    reveal(opaque_mul);

    let overhead = Journal::<TrustedKvPermission, PM>::journal_entry_overhead();
    let overhead_times_four = OverflowingU64::new(overhead).mul(4);
    let eight_u64_size = size_of::<u64>() * 8;
    let bytes_per_operation = overhead_times_four.add_usize(size_of::<L>()).add_usize(eight_u64_size);
    OverflowingU64::new(ps.max_operations_per_transaction).mul_overflowing_u64(&bytes_per_operation)
}

pub(super) open spec fn local_spec_space_needed_for_setup<PM, K, I, L>(ps: SetupParameters) -> nat
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    recommends
        ps.valid(),
{
    let journal_capacity = spec_space_needed_for_journal_capacity::<PM, K, I, L>(ps);
    let journal_end = Journal::<TrustedKvPermission, PM>::spec_space_needed_for_setup(journal_capacity);
    let sm_start = round_up_to_alignment(journal_end as int, KvStaticMetadata::spec_align_of() as int);
    let sm_end = sm_start + KvStaticMetadata::spec_size_of();
    let sm_crc_end = sm_end + u64::spec_size_of();
    let key_table_end = sm_crc_end + KeyTable::<PM, K>::spec_space_needed_for_setup(ps, sm_crc_end as nat);
    let item_table_end = key_table_end + ItemTable::<PM, I>::spec_space_needed_for_setup(ps, key_table_end as nat);
    let list_table_end = item_table_end + ListTable::<PM, L>::spec_space_needed_for_setup(ps, item_table_end as nat);
    list_table_end as nat
}

pub(super) exec fn local_space_needed_for_setup<PM, K, I, L>(ps: &SetupParameters)
                                                            -> (result: Result<u64, KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    ensures
        match result {
            Ok(v) => v == local_spec_space_needed_for_setup::<PM, K, I, L>(*ps),
            Err(KvError::InvalidParameter) => !ps.valid(),
            Err(KvError::OutOfSpace) => local_spec_space_needed_for_setup::<PM, K, I, L>(*ps) > u64::MAX,
            Err(_) => false,
        },
{
    if !exec_check_setup_parameters(ps) {
        return Err(KvError::InvalidParameter);
    }

    let journal_capacity = space_needed_for_journal_capacity::<PM, K, I, L>(ps);
    let journal_end = Journal::<TrustedKvPermission, PM>::space_needed_for_setup(&journal_capacity);
    let sm_start = journal_end.align(align_of::<KvStaticMetadata>());
    let sm_end = sm_start.add_usize(size_of::<KvStaticMetadata>());
    let sm_crc_end = sm_end.add_usize(size_of::<u64>());
    let key_table_size = KeyTable::<PM, K>::space_needed_for_setup(ps, &sm_crc_end);
    let key_table_end = sm_crc_end.add_overflowing_u64(&key_table_size);
    let item_table_size = ItemTable::<PM, I>::space_needed_for_setup(ps, &key_table_end);
    let item_table_end = key_table_end.add_overflowing_u64(&item_table_size);
    let list_table_size = ListTable::<PM, L>::space_needed_for_setup(ps, &item_table_end);
    let list_table_end = item_table_end.add_overflowing_u64(&list_table_size);
    assert(list_table_end@ == local_spec_space_needed_for_setup::<PM, K, I, L>(*ps));
    if list_table_end.is_overflowed() {
        Err(KvError::OutOfSpace)
    }
    else {
        Ok(list_table_end.unwrap())
    }
}

pub(super) exec fn write_static_metadata<PM>(
    pm: &mut PM,
    sm: &KvStaticMetadata,
    jc: &JournalConstants,
)
    where
        PM: PersistentMemoryRegion,
    requires
        old(pm).inv(),
        validate_static_metadata(*sm, *jc),
        jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() <= jc.app_area_end,
        jc.app_area_end <= old(pm)@.len(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, jc.app_area_start as int,
                                   jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()),
        recover_static_metadata(pm@.read_state, *jc) == Some(*sm),
{
    broadcast use axiom_bytes_len, axiom_to_from_bytes; //pmcopy_axioms;
    broadcast use group_update_bytes_effect;

    let sm_addr = jc.app_area_start;
    let sm_crc_addr = jc.app_area_start + size_of::<KvStaticMetadata>() as u64;
    let sm_crc = calculate_crc(sm);
    pm.serialize_and_write(sm_addr, sm);
    pm.serialize_and_write(sm_crc_addr, &sm_crc);
    assert(recover_static_metadata(pm@.read_state, *jc) =~= Some(*sm));
}

#[verifier::rlimit(20)]
pub(super) exec fn local_setup<PM, K, I, L>(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError<K>>)
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
            Err(KvError::InvalidParameter) => !ps.valid(),
            Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
            Err(KvError::OutOfSpace) => pm@.len() < local_spec_space_needed_for_setup::<PM, K, I, L>(*ps),
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

    let journal_capacity = space_needed_for_journal_capacity::<PM, K, I, L>(ps);
    let journal_end = Journal::<TrustedKvPermission, PM>::space_needed_for_setup(&journal_capacity);
    let sm_start = journal_end.align(align_of::<KvStaticMetadata>());
    let sm_end = sm_start.add_usize(size_of::<KvStaticMetadata>());
    let sm_crc_end = sm_end.add_usize(size_of::<u64>());
    if sm_crc_end.is_overflowed() {
        return Err(KvError::OutOfSpace);
    }
    if sm_crc_end.unwrap() > pm_size {
        return Err(KvError::OutOfSpace);
    }

    proof {
        broadcast use group_update_bytes_effect;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    }

    let key_sm = match KeyTable::<PM, K>::setup(pm, ps, sm_crc_end.unwrap(), pm_size) {
        Ok(key_sm) => key_sm,
        Err(e) => { return Err(e); },
    };
    let ghost state_after_key_init = pm@.read_state;

    let item_sm = match ItemTable::<PM, I>::setup::<K>(pm, ps, key_sm.table.end, pm_size) {
        Ok(item_sm) => item_sm,
        Err(e) => { return Err(e); },
    };
    let ghost state_after_item_init = pm@.read_state;

    let list_sm = match ListTable::<PM, L>::setup::<K>(pm, ps, item_sm.table.end, pm_size) {
        Ok(list_sm) => list_sm,
        Err(e) => { return Err(e); },
    };
    let ghost state_after_list_init = pm@.read_state;

    let kv_sm = KvStaticMetadata {
        encoded_policies: encode_policies(&ps.logical_range_gaps_policy),
        keys: key_sm,
        items: item_sm,
        lists: list_sm,
        id: ps.kvstore_id,
    };

    let jc = JournalConstants {
        app_program_guid: KVSTORE_PROGRAM_GUID,
        app_version_number: KVSTORE_PROGRAM_VERSION_NUMBER,
        journal_capacity: journal_capacity.unwrap(),
        app_area_start: sm_start.unwrap(),
        app_area_end: pm_size,
    };

    write_static_metadata::<PM>(pm, &kv_sm, &jc);
    let ghost state_after_sm_init = pm@.read_state;
    
    match Journal::<TrustedKvPermission, PM>::setup(pm, &jc) {
        Ok(jc) => {},
        Err(_) => { assert(false); return Err(KvError::InternalError); },
    };

    let ghost empty_keys = KeyTableSnapshot::<K>::init();
    assert(recover_static_metadata(pm@.read_state, jc) == Some(kv_sm)) by {
        assert(seqs_match_in_range(state_after_sm_init, pm@.read_state, jc.app_area_start as int,
                                   jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()));
    }
    assert(KeyTable::<PM, K>::recover(pm@.read_state, key_sm) == Some(empty_keys)) by {
        KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(state_after_key_init, pm@.read_state, key_sm);
    }
    assert(ItemTable::<PM, I>::recover(pm@.read_state, empty_keys.item_addrs(), item_sm)
           == Some(ItemTableSnapshot::<I>::init())) by {
        ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(state_after_item_init, pm@.read_state,
                                                                  empty_keys.item_addrs(), item_sm);
    }
    assert(ListTable::<PM, L>::recover(pm@.read_state, empty_keys.list_addrs(), list_sm)
           == Some(ListTableSnapshot::<L>::init())) by {
        ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(state_after_list_init, pm@.read_state,
                                                                  empty_keys.list_addrs(), list_sm);
    }

    assert(recover_kv::<PM, K, I, L>(pm@.read_state, jc)
           =~= Some(AtomicKvStore::<K, I, L>::init(ps.kvstore_id, ps.logical_range_gaps_policy)));
    Ok(())
}

}
