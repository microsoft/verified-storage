//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use core::hash::Hash;
use std::f64::MIN;
use std::num;
use crate::kv::durable::durableimpl_v::DurableKvStore;
use crate::kv::durable::maintablelayout_v::ListEntryMetadata;
use crate::kv::layout_v::*;
use crate::log2::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use super::kvimpl_t::KvError;

verus! {

pub open spec fn overall_metadata_valid<K, I, L>(
    overall_metadata: OverallMetadata,
    overall_metadata_addr: u64,
    kvstore_id: u128,
) -> bool
where
    K: PmCopy,
    I: PmCopy,
    L: PmCopy,
{
    &&& overall_metadata.kvstore_id == kvstore_id
    &&& overall_metadata.list_element_size == L::spec_size_of()
    &&& overall_metadata.item_size == I::spec_size_of()
    &&& overall_metadata.key_size == K::spec_size_of()
    &&& overall_metadata.main_table_entry_size ==
        ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of()
    // TODO: Check minimum log entry size
    &&& overall_metadata.num_keys > 0
    &&& overall_metadata.num_list_entries_per_node > 0
    &&& overall_metadata_addr >= VersionMetadata::spec_size_of() + u64::spec_size_of()
    &&& overall_metadata.main_table_addr >= overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of()
    &&& overall_metadata.main_table_size >= overall_metadata.num_keys * overall_metadata.main_table_entry_size
    &&& overall_metadata.item_table_addr >= overall_metadata.main_table_addr + overall_metadata.main_table_size
    &&& overall_metadata.item_table_size >= overall_metadata.num_keys * (overall_metadata.item_size + u64::spec_size_of())
    &&& overall_metadata.list_area_addr >= overall_metadata.item_table_addr + overall_metadata.item_table_size
    &&& overall_metadata.list_area_size >= overall_metadata.num_list_nodes * overall_metadata.list_node_size
    &&& overall_metadata.log_area_addr >= overall_metadata.list_area_addr + overall_metadata.list_area_size
    &&& overall_metadata.log_area_size >= overall_metadata.log_entry_size
    &&& overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE
    &&& overall_metadata.log_area_size > spec_log_area_pos() >= spec_log_header_area_size() > 0
    &&& overall_metadata.region_size >= overall_metadata.log_area_addr + overall_metadata.log_area_size
    &&& overall_metadata.region_size <= u64::MAX
    &&& overall_metadata.main_table_addr as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.main_table_size as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.item_table_addr as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.item_table_size as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.list_area_addr as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.list_area_size as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.log_area_addr as int % const_persistence_chunk_size() == 0
    &&& overall_metadata.log_area_size as int % const_persistence_chunk_size() == 0
    
}

// This function evaluates whether memory was correctly set up.
// It's a helpful specification function for use in later
// functions in this file.
//
// Because answering this question depends on knowing various
// metadata about this region and the log it's part of, the
// function needs various input parameters for that. Its
// parameters are:
//
// `mem` -- the contents of memory for this region
// `region_size` -- how big this region is
// `log_id` -- the GUID of the log it's being used for
pub open spec fn memory_correctly_set_up_on_region<K, I, L>(
    mem: Seq<u8>,
    kvstore_id: u128,
) -> bool
where
    K: PmCopy,
    I: PmCopy,
    L: PmCopy,
{
    let version_metadata = deserialize_version_metadata(mem);
    let version_crc = deserialize_version_crc(mem);
    let overall_metadata = deserialize_overall_metadata(mem, version_metadata.overall_metadata_addr);
    let overall_crc = deserialize_overall_crc(mem, version_metadata.overall_metadata_addr);
    &&& mem.len() >= VersionMetadata::spec_size_of() + u64::spec_size_of()
    &&& version_crc == version_metadata.spec_crc()
    &&& overall_crc == overall_metadata.spec_crc()
    &&& version_metadata_valid(version_metadata)
    &&& overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, kvstore_id)
    &&& overall_metadata.region_size <= mem.len()

    &&& VersionMetadata::bytes_parseable(extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_METADATA as nat, VersionMetadata::spec_size_of()))
    &&& u64::bytes_parseable(extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_CRC as nat, u64::spec_size_of()))
    &&& OverallMetadata::bytes_parseable(extract_bytes(mem, version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()))
    &&& u64::bytes_parseable(extract_bytes(mem, (version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of()) as nat, u64::spec_size_of()))
}

pub open spec fn version_metadata_valid(version_metadata: VersionMetadata) -> bool 
{
    &&& version_metadata.program_guid == KVSTORE_PROGRAM_GUID
    &&& version_metadata.version_number == KVSTORE_PROGRAM_VERSION_NUMBER
    &&& version_metadata.overall_metadata_addr >= ABSOLUTE_POS_OF_VERSION_METADATA + u64::spec_size_of()
}

#[inline]
fn round_up_to_multiple_of_256(n: u64) -> (result: u64)
    requires
        n <= u64::MAX - 256,
    ensures
        result >= n,
{
    let remainder = n % 256;
    if remainder == 0 {
        n
    } else {
        n + 256 - remainder
    }
}

pub fn initialize_overall_metadata<K, I, L> (
    region_size: u64,
    overall_metadata_addr: u64,
    kvstore_id: u128,
    num_keys: u64,
    num_list_entries_per_node: u32,
    num_list_nodes: u64,
) -> (result: Result<OverallMetadata, KvError<K>>)
    where
        K: PmCopy + std::fmt::Debug,
        I: PmCopy,
        L: PmCopy,
    ensures
        match result {
            Ok(overall_metadata) => {
                &&& overall_metadata.region_size == region_size
                &&& overall_metadata.kvstore_id == kvstore_id
                &&& overall_metadata_valid::<K, I, L>(overall_metadata, overall_metadata_addr, kvstore_id)
            },
            Err(_) => true,
        },
{
    if size_of::<L>() > u32::MAX as usize {
        return Err(KvError::ListElementSizeTooBig);
    }
    let list_element_size = size_of::<L>() as u32;
    if size_of::<I>() > u32::MAX as usize {
        return Err(KvError::ItemSizeTooBig);
    }
    let item_size = size_of::<I>() as u64;
    if size_of::<K>() > u32::MAX as usize {
        return Err(KvError::KeySizeTooBig);
    }
    let key_size = size_of::<K>() as u32;
    assert(u64::spec_size_of() == 8) by { reveal(spec_padding_needed); }
    assert(ListEntryMetadata::spec_size_of() < 10000) by { reveal(spec_padding_needed); }
    let list_entry_metadata_size = size_of::<ListEntryMetadata>() as u32;
    if key_size > u32::MAX - 2 * size_of::<u64>() as u32 - list_entry_metadata_size {
        return Err(KvError::KeySizeTooBig)
    }
    let main_table_entry_size: u32 = list_entry_metadata_size + key_size + 2 * size_of::<u64>() as u32;
    let log_entry_size: u32 = 8; // TODO - Calculate this
    if num_list_entries_per_node as u64 > u64::MAX / (list_element_size as u64 + size_of::<u64>() as u64) {
        return Err(KvError::TooManyListEntriesPerNode);
    }
    assert(num_list_entries_per_node * (list_element_size + u64::spec_size_of() as u64) <= u64::MAX) by {
        assert({
                   &&& num_list_entries_per_node <= u64::MAX as int / (list_element_size + u64::spec_size_of())
                   &&& list_element_size <= u32::MAX
                   &&& u64::spec_size_of() == 8
               } ==> num_list_entries_per_node * (list_element_size + u64::spec_size_of()) <= u64::MAX) by
            (nonlinear_arith);
    }
    let list_node_size: u64 = num_list_entries_per_node as u64 * (list_element_size as u64 + size_of::<u64>() as u64);
    if overall_metadata_addr >= u64::MAX - size_of::<OverallMetadata>() as u64 {
        return Err(KvError::InternalError);
    }
    if overall_metadata_addr + size_of::<OverallMetadata>() as u64 >= u64::MAX - size_of::<u64>() as u64 {
        return Err(KvError::InternalError);
    }
    if overall_metadata_addr + size_of::<OverallMetadata>() as u64 + size_of::<u64>() as u64 > u64::MAX - 256 {
        return Err(KvError::InternalError);
    }
    let main_table_addr: u64 = round_up_to_multiple_of_256(overall_metadata_addr +
                                                           size_of::<OverallMetadata>() as u64 +
                                                           size_of::<u64>() as u64);
    if num_keys < 1 {
        return Err(KvError::TooFewKeys);
    }
    if num_keys > u64::MAX / main_table_entry_size as u64 {
        return Err(KvError::TooManyKeys);
    }

    assert(num_keys <= u64::MAX as int / main_table_entry_size as int ==>
           num_keys * main_table_entry_size <= u64::MAX) by (nonlinear_arith);
    let main_table_size: u64 = num_keys as u64 * main_table_entry_size as u64;
    if main_table_size as usize > usize::MAX - main_table_addr as usize {
        return Err(KvError::TooManyKeys);
    }
    let required_size: usize = main_table_addr as usize + main_table_size as usize;
    if required_size > region_size as usize {
        return Err(KvError::RegionTooSmall { required: required_size, actual: region_size as usize });
    }

    if main_table_addr >= u64::MAX - 256 || main_table_size > u64::MAX - main_table_addr - 256 {
        return Err(KvError::TooManyKeys);
    }
    let item_table_addr: u64 = round_up_to_multiple_of_256(main_table_addr + main_table_size);
    let item_slot_size : u64 = item_size + size_of::<u64>() as u64;
    if num_keys > u64::MAX / item_slot_size {
        return Err(KvError::TooManyKeys);
    }
    assert(num_keys <= u64::MAX as int / item_slot_size as int ==>
            num_keys * item_slot_size <= u64::MAX as int) 
    by {
        // First, establish (u64::MAX / item_slot_size) * item_slot_size == u64::MAX - u64::MAX % item_slot_size
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u64::MAX as int, item_slot_size as int);
        // Second, establish num_keys * item_slot_size <= (u64::MAX / item_slot_size) * item_slot_size
        vstd::arithmetic::mul::lemma_mul_inequality(num_keys as int, (u64::MAX / item_slot_size) as int, item_slot_size as int);
    }
    let item_table_size: u64 = num_keys * item_slot_size;

    if item_table_size > u64::MAX - item_table_addr {
        return Err(KvError::TooManyKeys);
    }
    let required_size = item_table_addr as usize + item_table_size as usize;
    if required_size > region_size as usize {
        return Err(KvError::RegionTooSmall { required: required_size, actual: region_size as usize });
    }
    if item_table_addr >= u64::MAX - 256 || item_table_size > u64::MAX - item_table_addr - 256 {
        return Err(KvError::TooManyKeys);
    }
    let list_area_addr: u64 = round_up_to_multiple_of_256(item_table_addr + item_table_size);

    if list_node_size > 0 {
        if num_list_nodes > u64::MAX / list_node_size as u64 {
            return Err(KvError::TooManyListNodes);
        }
        assert(num_list_nodes <= u64::MAX as int / (list_node_size as int) ==>
               num_list_nodes * list_node_size <= u64::MAX as int) by (nonlinear_arith);
    }
    else {
        assert(num_list_nodes * list_node_size == 0) by {
            vstd::arithmetic::mul::lemma_mul_basics(num_list_nodes as int);
        }
    }
    let list_area_size: u64 = num_list_nodes * list_node_size;

    if list_area_size > u64::MAX - list_area_addr {
        return Err(KvError::TooManyListNodes);
    }
    let required_size = list_area_addr as usize + list_area_size as usize;
    if required_size > region_size as usize {
        return Err(KvError::RegionTooSmall { required: required_size, actual: region_size as usize });
    }
    if list_area_addr >= u64::MAX - 256 || list_area_size > u64::MAX - list_area_addr - 256 {
        return Err(KvError::TooManyListNodes);
    }
    let log_area_addr: u64 = round_up_to_multiple_of_256(list_area_addr + list_area_size);
    let log_area_size = log_entry_size as u64; // TODO - Make this bigger

    if log_area_size > u64::MAX - log_area_addr {
        return Err(KvError::TooManyKeys);
    }
    assert(LogMetadata::spec_size_of() * 2 <= u64::MAX) by (compute_only);
    assert(u64::spec_size_of() + LogMetadata::spec_size_of() * 2 <= u64::MAX) by (compute_only);
    assert(u64::spec_size_of() + LogMetadata::spec_size_of() * 2 + u64::spec_size_of() * 2 <= u64::MAX) by (compute_only);
    if log_area_size < log_header_area_size() + MIN_LOG_AREA_SIZE {
        return Err(KvError::LogAreaTooSmall { required: (log_header_area_size() + MIN_LOG_AREA_SIZE) as usize, actual: log_area_size as usize });
    }
    let required_size = log_area_addr as usize + log_area_size as usize;
    if required_size > region_size as usize {
        return Err(KvError::RegionTooSmall { required: required_size, actual: region_size as usize });
    }

    assert(region_size >= main_table_addr + main_table_size);

    let overall_metadata = OverallMetadata{
        region_size,
        kvstore_id,
        key_size,
        item_size,
        list_element_size,
        main_table_entry_size,
        log_entry_size,
        num_keys,
        num_list_entries_per_node,
        list_node_size,
        num_list_nodes,
        main_table_addr,
        main_table_size,
        item_table_addr,
        item_table_size,
        list_area_addr,
        list_area_size,
        log_area_addr,
        log_area_size,
    };
    
    Ok(overall_metadata)
}

pub fn setup<PM, K, I, L> (
    pm: &mut PM,
    kvstore_id: u128,
    num_keys: u64,
    num_list_entries_per_node: u32,
    num_list_nodes: u64,
) -> (result: Result<(VersionMetadata, OverallMetadata), KvError<K>>)
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug + Copy,
    requires
        old(pm).inv(),
        old(pm)@.flush_predicted(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        pm@.len() == old(pm)@.len(),
        match result {
            Ok((version_metadata, overall_metadata)) => {
                &&& memory_correctly_set_up_on_region::<K, I, L>(pm@.durable_state, kvstore_id)
                &&& pm@.flush_predicted()

                &&& deserialize_version_metadata(pm@.durable_state) == version_metadata
                &&& deserialize_version_crc(pm@.durable_state) == version_metadata.spec_crc()
                &&& deserialize_overall_metadata(pm@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata
                &&& deserialize_overall_crc(pm@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata.spec_crc()
                &&& overall_metadata.region_size == pm@.len()
            },
            Err(_) => true,
        },
{
    let region_size = pm.get_region_size();

    assert(VersionMetadata::spec_size_of() <= ABSOLUTE_POS_OF_VERSION_CRC) by (compute_only);

    let overall_metadata_addr = ABSOLUTE_POS_OF_VERSION_CRC + size_of::<u64>() as u64;

    // TODO: use `overall_metadata_addr` directly in this assertion if/when assert by compute_only gets local variables in its context
    assert(ABSOLUTE_POS_OF_VERSION_CRC + u64::spec_size_of()  + OverallMetadata::spec_size_of() + u64::spec_size_of() <= u64::MAX) by (compute_only);
    if region_size < overall_metadata_addr + size_of::<OverallMetadata>() as u64 + size_of::<u64>() as u64 {
        return Err(KvError::RegionTooSmall{
            required: overall_metadata_addr as usize + size_of::<OverallMetadata>() + size_of::<u64>(),
            actual: region_size as usize,
        });
    }

    let version_metadata = VersionMetadata{
        program_guid: KVSTORE_PROGRAM_GUID,
        version_number: KVSTORE_PROGRAM_VERSION_NUMBER,
        overall_metadata_addr,
    };
    let version_crc = calculate_crc(&version_metadata);
    let overall_metadata = initialize_overall_metadata::<K, I, L>(
        region_size, overall_metadata_addr, kvstore_id, num_keys, num_list_entries_per_node, num_list_nodes
    )?;
    let overall_crc = calculate_crc(&overall_metadata);

    pm.serialize_and_write(ABSOLUTE_POS_OF_VERSION_METADATA, &version_metadata);
    pm.serialize_and_write(ABSOLUTE_POS_OF_VERSION_CRC, &version_crc);
    pm.serialize_and_write(version_metadata.overall_metadata_addr, &overall_metadata);
    pm.serialize_and_write(version_metadata.overall_metadata_addr + size_of::<OverallMetadata>() as u64, &overall_crc);
    pm.flush();
    
    proof {
        broadcast use pmcopy_axioms;

        let mem = pm@.durable_state;
        assert(version_metadata.spec_to_bytes() == extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_METADATA as nat, VersionMetadata::spec_size_of()));
        assert(version_crc.spec_to_bytes() == extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_CRC as nat, u64::spec_size_of()));
        assert(overall_metadata.spec_to_bytes() == extract_bytes(mem, version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()));
        assert(overall_crc.spec_to_bytes() == extract_bytes(mem, (version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of()) as nat, u64::spec_size_of()));
    }

    Ok((version_metadata, overall_metadata))
}

pub exec fn read_version_metadata<PM, K, I, L>(pm: &PM, kvstore_id: u128) -> (result: Result<VersionMetadata, KvError<K>>)
    where 
        PM: PersistentMemoryRegion,
        K: PmCopy + std::fmt::Debug,
        I: PmCopy,
        L: PmCopy,
    requires 
        pm.inv(),
        pm@.flush_predicted(),
        0 <= ABSOLUTE_POS_OF_VERSION_METADATA < ABSOLUTE_POS_OF_VERSION_METADATA + VersionMetadata::spec_size_of() <= pm@.len(),
        memory_correctly_set_up_on_region::<K, I, L>(pm@.durable_state, kvstore_id),
    ensures 
        match result {
            Ok(version_metadata) => 
                version_metadata == deserialize_version_metadata(pm@.durable_state),
            Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
            Err(_) => false,
        }
{
    let ghost mem = pm@.durable_state;
    let ghost true_version_metadata_bytes = extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_METADATA as nat, VersionMetadata::spec_size_of());

    let maybe_corrupted_version_metadata = match pm.read_aligned::<VersionMetadata>(ABSOLUTE_POS_OF_VERSION_METADATA) {
        Ok(bytes) => bytes,
        Err(e) => {
            assert(false);
            return Err(KvError::PmemErr { pmem_err: e });
        }
    };
    let maybe_corrupted_crc = match pm.read_aligned::<u64>(ABSOLUTE_POS_OF_VERSION_CRC) {
        Ok(bytes) => bytes,
        Err(e) => {
            assert(false);
            return Err(KvError::PmemErr { pmem_err: e });
        }
    };

    if !check_crc(maybe_corrupted_version_metadata.as_slice(), maybe_corrupted_crc.as_slice(),
                  Ghost(true_version_metadata_bytes),
                  Ghost(pm.constants().impervious_to_corruption()),
                  Ghost(ABSOLUTE_POS_OF_VERSION_METADATA as int),
                  Ghost(ABSOLUTE_POS_OF_VERSION_CRC as int))
    {
        return Err(KvError::CRCMismatch);
    }
    let version_metadata = maybe_corrupted_version_metadata.extract_init_val(Ghost(VersionMetadata::spec_from_bytes(true_version_metadata_bytes)));
    Ok(*version_metadata)
}

pub exec fn read_overall_metadata<PM, K, I, L>(pm: &PM, version_metadata: &VersionMetadata, kvstore_id: u128) -> (result: Result<OverallMetadata, KvError<K>>)
    where 
        PM: PersistentMemoryRegion,
        K: PmCopy + std::fmt::Debug,
        I: PmCopy,
        L: PmCopy,
    requires 
        pm.inv(),
        pm@.flush_predicted(),
        version_metadata == deserialize_version_metadata(pm@.durable_state),
        0 <= version_metadata.overall_metadata_addr < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() < 
            version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of() <= pm@.len() <= u64::MAX,
        memory_correctly_set_up_on_region::<K, I, L>(pm@.durable_state, kvstore_id),
    ensures 
        match result {
            Ok(overall_metadata) => overall_metadata == deserialize_overall_metadata(pm@.durable_state, version_metadata.overall_metadata_addr),
            Err(KvError::CRCMismatch) => !pm.constants().impervious_to_corruption(),
            Err(_) => false,
        }
{
    let ghost mem = pm@.durable_state;
    let metadata_addr = version_metadata.overall_metadata_addr;
    let crc_addr = metadata_addr + size_of::<OverallMetadata>() as u64;

    let ghost metadata_addrs = Seq::new(OverallMetadata::spec_size_of(), |i: int| metadata_addr + i);
    let ghost true_overall_metadata_bytes = extract_bytes(mem, metadata_addr as nat, OverallMetadata::spec_size_of());

    let maybe_corrupted_overall_metadata = match pm.read_aligned::<OverallMetadata>(metadata_addr) {
        Ok(bytes) => bytes,
        Err(e) => {
            assert(false);
            return Err(KvError::PmemErr { pmem_err: e });
        }
    };
    let maybe_corrupted_crc = match pm.read_aligned::<u64>(crc_addr) {
        Ok(bytes) => bytes,
        Err(e) => {
            assert(false);
            return Err(KvError::PmemErr { pmem_err: e });
        }
    };

    if !check_crc(maybe_corrupted_overall_metadata.as_slice(), maybe_corrupted_crc.as_slice(),
                  Ghost(true_overall_metadata_bytes),
                  Ghost(pm.constants().impervious_to_corruption()),
                  Ghost(metadata_addr as int),
                  Ghost(crc_addr as int))
    {
        return Err(KvError::CRCMismatch);
    }
    let overall_metadata = maybe_corrupted_overall_metadata.extract_init_val(Ghost(OverallMetadata::spec_from_bytes(true_overall_metadata_bytes)));
    Ok(*overall_metadata)
}
}
