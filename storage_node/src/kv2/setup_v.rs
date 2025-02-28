#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::CheckedU64;
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
use super::*;
use super::keys::*;
use super::impl_t::*;
use super::items::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

exec fn check_setup_parameters(ps: &SetupParameters) -> (result: bool)
    ensures
        result == ps.valid(),
{
    if ps.max_keys == 0 { false }
    else if ps.max_list_entries == 0 { false }
    else if ps.max_operations_per_transaction == 0 { false }
    else { true }
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn space_needed_for_journal_capacity(ps: &SetupParameters) -> (result: CheckedU64)
        ensures
            result@ == Self::spec_space_needed_for_journal_capacity(*ps),
    {
        let overhead = Journal::<TrustedKvPermission, PM>::journal_entry_overhead();
        let overhead_times_four = CheckedU64::new(overhead).mul(4);
        let eight_u64_size = size_of::<u64>() * 8;
        let bytes_per_operation = overhead_times_four.add(eight_u64_size as u64);
        CheckedU64::new(ps.max_operations_per_transaction).mul_checked(&bytes_per_operation)
    }
    
    pub exec fn space_needed_for_setup(ps: &SetupParameters) -> (result: Result<u64, KvError>)
        where
            PM: PersistentMemoryRegion,
            K: Hash + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(*ps),
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::OutOfSpace) => Self::spec_space_needed_for_setup(*ps) > u64::MAX,
                Err(_) => false,
            },
    {
        if !check_setup_parameters(ps) {
            return Err(KvError::InvalidParameter);
        }
    
        let journal_capacity = Self::space_needed_for_journal_capacity(ps);
        let journal_end = Journal::<TrustedKvPermission, PM>::space_needed_for_setup(&journal_capacity);
        let sm_start = journal_end.align(align_of::<KvStaticMetadata>());
        let sm_end = sm_start.add(size_of::<KvStaticMetadata>() as u64);
        let sm_crc_end = sm_end.add(size_of::<u64>() as u64);
        let key_table_size = KeyTable::<PM, K>::space_needed_for_setup(ps, &sm_crc_end);
        let key_table_end = sm_crc_end.add_checked(&key_table_size);
        let item_table_size = ItemTable::<PM, I>::space_needed_for_setup(ps, &key_table_end);
        let item_table_end = key_table_end.add_checked(&item_table_size);
        let list_table_size = ListTable::<PM, L>::space_needed_for_setup(ps, &item_table_end);
        let list_table_end = item_table_end.add_checked(&list_table_size);
        assert(list_table_end@ == Self::spec_space_needed_for_setup(*ps));
        if list_table_end.is_overflowed() {
            Err(KvError::OutOfSpace)
        }
        else {
            Ok(list_table_end.unwrap())
        }
    }

    #[inline]
    exec fn write_static_metadata(
        pm: &mut PM,
        sm: &KvStaticMetadata,
        jc: &JournalConstants,
    )
        where
            PM: PersistentMemoryRegion,
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            validate_static_metadata::<K, I, L>(*sm, *jc),
            jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() <= jc.app_area_end,
            jc.app_area_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, jc.app_area_start as int,
                                       jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()),
            recover_static_metadata::<K, I, L>(pm@.read_state, *jc) == Some(*sm),
    {
        broadcast use pmcopy_axioms;
        broadcast use broadcast_can_result_from_write_effect_on_read_state;
        broadcast use broadcast_can_result_from_write_effect_on_read_state_subranges;
        reveal(recover_static_metadata);
    
        let sm_addr = jc.app_area_start;
        let sm_crc_addr = jc.app_area_start + size_of::<KvStaticMetadata>() as u64;
        let sm_crc = calculate_crc(sm);
        pm.serialize_and_write(sm_addr, sm);
        pm.serialize_and_write(sm_crc_addr, &sm_crc);
        assert(recover_static_metadata::<K, I, L>(pm@.read_state, *jc) =~= Some(*sm));
    }
    
    pub exec fn setup(pm: &mut PM, ps: &SetupParameters) -> (result: Result<(), KvError>)
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
                    &&& Self::recover(pm@.durable_state)
                        == Some(AtomicKvStore::<K, I, L>::init(ps.kvstore_id, ps.logical_range_gaps_policy))
                },
                Err(KvError::InvalidParameter) => !ps.valid(),
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) => pm@.len() < Self::spec_space_needed_for_setup(*ps),
                Err(_) => false,
            },
    {
        if !check_setup_parameters(ps) {
            return Err(KvError::InvalidParameter);
        }
    
        proof {
            pm.lemma_inv_implies_view_valid();
        }
    
        let pm_size = pm.get_region_size();
    
        let journal_capacity = Self::space_needed_for_journal_capacity(ps);
        let journal_end = Journal::<TrustedKvPermission, PM>::space_needed_for_setup(&journal_capacity);
        let sm_start = journal_end.align(align_of::<KvStaticMetadata>());
        let sm_end = sm_start.add(size_of::<KvStaticMetadata>() as u64);
        let sm_crc_end = sm_end.add(size_of::<u64>() as u64);
        if sm_crc_end.is_overflowed() {
            return Err(KvError::OutOfSpace);
        }
        if sm_crc_end.unwrap() > pm_size {
            return Err(KvError::OutOfSpace);
        }
    
        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        }
    
        let key_sm = match KeyTable::<PM, K>::setup(pm, ps, sm_crc_end.unwrap(), pm_size) {
            Ok(key_sm) => key_sm,
            Err(e) => { return Err(e); },
        };
        let ghost state_after_key_init = pm@.read_state;
    
        let item_sm = match ItemTable::<PM, I>::setup(pm, ps, key_sm.end(), pm_size) {
            Ok(item_sm) => item_sm,
            Err(e) => { return Err(e); },
        };
        let ghost state_after_item_init = pm@.read_state;
    
        let list_sm = match ListTable::<PM, L>::setup(pm, ps, item_sm.end(), pm_size) {
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
    
        Self::write_static_metadata(pm, &kv_sm, &jc);
        let ghost state_after_sm_init = pm@.read_state;
        
        match Journal::<TrustedKvPermission, PM>::setup(pm, &jc) {
            Ok(jc) => {},
            Err(_) => { assert(false); return Err(KvError::InternalError); },
        };
    
        let ghost empty_keys = KeyTableSnapshot::<K>::init();
        assert(recover_static_metadata::<K, I, L>(pm@.read_state, jc) == Some(kv_sm)) by {
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(state_after_sm_init, pm@.read_state,
                                                                              kv_sm, jc);
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
    
}
