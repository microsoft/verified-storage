//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use core::hash::Hash;
use crate::kv::durable::metadata::layout_v::ListEntryMetadata;
use crate::kv::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

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
    spec fn memory_correctly_set_up_on_region<K, I, L>(
        mem: Seq<u8>,
        region_size: u64,
        kvstore_id: u128,
    ) -> bool
    where
        K: PmCopy,
        I: PmCopy,
        L: PmCopy,
    {
        let version_metadata = deserialize_version_metadata(mem);
        let version_crc = deserialize_version_crc(mem);
        let overall_metadata = deserialize_overall_metadata(mem);
        let overall_crc = deserialize_overall_crc(mem);
        &&& mem.len() >= ABSOLUTE_POS_OF_OVERALL_CRC + u64::spec_size_of()
        &&& mem.len() == region_size
        &&& version_crc == version_metadata.spec_crc()
        &&& overall_crc == overall_metadata.spec_crc()
        &&& version_metadata.program_guid == KVSTORE_PROGRAM_GUID
        &&& version_metadata.version_number == KVSTORE_PROGRAM_VERSION_NUMBER
        &&& version_metadata.length_of_overall_metadata == OverallMetadata::spec_size_of()
        &&& overall_metadata.region_size == region_size
        &&& overall_metadata.kvstore_id == kvstore_id
        &&& overall_metadata.list_element_size == L::spec_size_of()
        &&& overall_metadata.item_size == I::spec_size_of()
        &&& overall_metadata.metadata_node_size ==
            ListEntryMetadata::spec_size_of() + u64::spec_size_of() + u64::spec_size_of() + K::spec_size_of()
        // TODO: Check minimum log entry size
        &&& overall_metadata.num_keys > 0
        &&& overall_metadata.metadata_table_addr >= ABSOLUTE_POS_OF_OVERALL_CRC + u64::spec_size_of()
        &&& overall_metadata.metadata_table_size >= overall_metadata.metadata_node_size * overall_metadata.num_keys
        &&& overall_metadata.item_table_addr >=
            overall_metadata.metadata_table_addr + overall_metadata.metadata_table_size
        &&& overall_metadata.item_table_size >= overall_metadata.item_size * overall_metadata.num_keys
        &&& overall_metadata.list_area_addr >= overall_metadata.item_table_addr + overall_metadata.item_table_size
        &&& overall_metadata.list_area_size >= overall_metadata.list_node_size * overall_metadata.num_list_nodes
        &&& overall_metadata.log_area_addr >= overall_metadata.list_area_addr + overall_metadata.list_area_size
        &&& overall_metadata.log_area_size >= overall_metadata.log_entry_size
    }

}
