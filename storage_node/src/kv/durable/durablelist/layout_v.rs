//! This file describes the persistent-memory layout of the
//! durable list implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//!
//!

use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::prelude::*;

verus! {
    // These constants describe the position of various parts
    // of the durable list structures on persistent memory.
    // Note that the durable list uses multiple persistent
    // memory regions.

    // List metadata region
    // Starts with a metadata header that is written at setup and
    // subsequently immutable.
    pub const ABSOLUTE_POS_OF_METADATA_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_ELEMENT_SIZE: u64 = 0;
    pub const RELATIVE_POS_OF_NODE_SIZE: u64 = 4;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64: 8;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 16;
    pub const LENGTH_OF_METADATA_HEADER: u64 = 32;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 32;

    // The current version number, and the only one whose contents
    // this program can read, is the following:
    pub const LIST_VERISON_NUMBER: u64 = 1;

    // This GUID was generated randomly and is meant to describe the
    // durable list program, even if it has future versions.
    pub const DURABLE_LIST_PROGRAM_GUID: u128 = 0xC357BD8AA950BDA76345F1DCEC7DBF3Fu128;

    #[repr(C)]
    pub struct GlobalListMetadata
    {
        pub element_size: u32,
        pub node_size: u32,
        pub version_number: u64,
        pub program_guid: u128,
    }

    // Per-entry relative offsets for list entry metadata
    // The list metadata region is an array of list entry metadata
    // structures, each of which contains metadata about the list
    // associated with a given key of type K. K must be Sized,
    // but we need to be generic over any K, so the key is the last
    // field of the structure to avoid layout weirdness

    pub const RELATIVE_POS_OF_ENTRY_METADATA_CRC: u64 = 0;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_HEAD: u64 = 8;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_TAIL: u64 = 16;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_LENGTH: u64 = 24;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET: u64 = 32;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_KEY: 40;


    #[repr(C)]
    pub struct ListEntryMetadata<K>
        where
            K: Sized
    {
        head: u64,
        tail: u64,
        length: u64,
        first_entry_offset: u64, // offset of the first live entry in the head node
        key: K,
    }

    // Per-node relative offsets for unrolled linked list nodes
    // Most list metadata is stored in the ListEntryMetadata structure,
    // so nodes only need to have a next pointer and a CRC for that
    // pointer. Since it's only 2 fields and one is a CRC, there is
    // no struct associated with the node metadata
    pub const RELATIVE_POS_OF_NEXT_POINTER: u64 = 0;
    pub const RELATIVE_POS_OF_LIST_NODE_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_LIST_CONTENTS_AREA: u64 = 16;
}
