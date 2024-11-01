//! This file describes the persistent-memory layout used by the
//! KV store implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//! The persistent-memory region used to store a KV store will have
//! the following layout.
//!
//! Version metadata:  Metadata whose length is constant across all versions
//! Overall metadata:  Overall metadata, notably the locations and sizes of
//!                    the following subregions.
//! Metadata table:    Table containing one entry per key
//! Item table:        Table containing items associated with keys
//! List area:         Nodes containing elements of lists associated with keys
//! Log area:          Log allowing atomic transactions
//!

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{PmSafe, PmSized, ConstPmSized, UnsafeSpecPmSized};
use crate::util_v::*;
use deps_hack::{PmCopy};
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    /// Constants

    // These constants describe the absolute or relative positions of
    // various parts of the layout.
    pub const ABSOLUTE_POS_OF_VERSION_METADATA: u64 = 0;
    pub const ABSOLUTE_POS_OF_VERSION_CRC: u64 = 32;

    // This GUID was generated randomly and is meant to describe the
    // KV store program, even if it has future versions.
    pub const KVSTORE_PROGRAM_GUID: u128 = 0x5380e95bfa3c40a5b59a217771724d11;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const KVSTORE_PROGRAM_VERSION_NUMBER: u64 = 1;

    // These structs represent the different levels of metadata.

    #[repr(C)]
    #[derive(PmCopy, Copy, Default)]
    pub struct VersionMetadata {
        pub version_number: u64,
        pub overall_metadata_addr: u64,
        pub program_guid: u128,
    }

    #[repr(C)]
    #[derive(PmCopy, Copy, Default)]
    pub struct OverallMetadata {
        pub key_size: u32, // K::size_of()
        pub list_element_size: u32, // L::size_of()
        pub main_table_entry_size: u32,
        pub log_entry_size: u32,
        pub num_list_entries_per_node: u32,
        pub item_size: u64, // I::size_of()
        pub region_size: u64,
        pub num_keys: u64,
        pub list_node_size: u64,
        pub num_list_nodes: u64,
        pub main_table_addr: u64,
        pub main_table_size: u64,
        pub item_table_addr: u64,
        pub item_table_size: u64,
        pub list_area_addr: u64,
        pub list_area_size: u64,
        pub log_area_addr: u64,
        pub log_area_size: u64,
        pub kvstore_id: u128,
    }

    /// Specification functions for extracting metadata from a
    /// persistent-memory region.

    // This function extracts the bytes encoding overall metadata from
    // the contents `mem` of a persistent memory region.
    pub open spec fn extract_version_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_METADATA as nat, VersionMetadata::spec_size_of())
    }

    pub open spec fn deserialize_version_metadata(mem: Seq<u8>) -> VersionMetadata
    {
        VersionMetadata::spec_from_bytes(extract_version_metadata(mem))
    }

    // This function extracts the CRC of the version metadata from the
    // contents `mem` of a persistent memory region.
    pub open spec fn extract_version_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_VERSION_CRC as nat, u64::spec_size_of())
    }

    pub open spec fn deserialize_version_crc(mem: Seq<u8>) -> u64
    {
        u64::spec_from_bytes(extract_version_crc(mem))
    }

    // This function extracts the bytes encoding overall metadata
    // from the contents `mem` of a persistent memory overall.
    pub open spec fn extract_overall_metadata(mem: Seq<u8>, overall_metadata_addr: u64) -> Seq<u8>
    {
        extract_bytes(mem, overall_metadata_addr as nat, OverallMetadata::spec_size_of())
    }

    pub open spec fn deserialize_overall_metadata(mem: Seq<u8>, overall_metadata_addr: u64) -> OverallMetadata
    {
        OverallMetadata::spec_from_bytes(extract_overall_metadata(mem, overall_metadata_addr))
    }

    // This function extracts the CRC of the overall metadata from the
    // contents `mem` of a persistent memory overall.
    pub open spec fn extract_overall_crc(mem: Seq<u8>, overall_metadata_addr: u64) -> Seq<u8>
    {
        let crc_addr = overall_metadata_addr + OverallMetadata::spec_size_of();
        extract_bytes(mem, crc_addr as nat, u64::spec_size_of())
    }

    pub open spec fn deserialize_overall_crc(mem: Seq<u8>, overall_metadata_addr: u64) -> u64
    {
        let bytes = extract_overall_crc(mem, overall_metadata_addr);
        u64::spec_from_bytes(bytes)
    }

    pub proof fn lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
        v1: PersistentMemoryRegionView,
        v2: PersistentMemoryRegionView,
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
    )
        requires
            v1.len() == v2.len(),
            version_metadata.overall_metadata_addr >= VersionMetadata::spec_size_of(),
            v1.len() >= version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of(),
            forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==> v1.state[addr] == v2.state[addr],
            forall|addr: int| version_metadata.overall_metadata_addr <= addr
                        < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                v1.state[addr] == v2.state[addr],
            forall|s| #[trigger] v1.can_crash_as(s) ==> version_metadata == deserialize_version_metadata(s),
            forall|s| #[trigger] v1.can_crash_as(s) ==>
                overall_metadata == deserialize_overall_metadata(s, version_metadata.overall_metadata_addr),
        ensures
            forall|s| #[trigger] v2.can_crash_as(s) ==> version_metadata == deserialize_version_metadata(s),
            forall|s| #[trigger] v2.can_crash_as(s) ==>
                overall_metadata == deserialize_overall_metadata(s, version_metadata.overall_metadata_addr),
    {
        assert forall|s2| #[trigger] v2.can_crash_as(s2) implies version_metadata == deserialize_version_metadata(s2) by
        {
            let f = |addr: int| !(0 <= addr < VersionMetadata::spec_size_of());
            let s1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(v2, v1, s2, f);
            assert(forall|addr: int| 0 <= addr < s1.len() && !f(addr) ==> s1[addr] == s2[addr]);
            lemma_establish_extract_bytes_equivalence(s1, s2);
            assert(deserialize_version_metadata(s1) =~= deserialize_version_metadata(s2));
        }
        
        assert forall|s2| #[trigger] v2.can_crash_as(s2) implies
            overall_metadata == deserialize_overall_metadata(s2, version_metadata.overall_metadata_addr) by
        {
            let f = |addr: int| !(version_metadata.overall_metadata_addr <= addr
                                < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of());
            let s1 = lemma_get_crash_state_given_one_for_other_view_differing_only_at_certain_addresses(v2, v1, s2, f);
            assert(forall|addr: int| 0 <= addr < s1.len() && !f(addr) ==> s1[addr] == s2[addr]);
            lemma_establish_extract_bytes_equivalence(s1, s2);
            assert(deserialize_version_metadata(s1) =~= deserialize_version_metadata(s2));
        }
    }
}
