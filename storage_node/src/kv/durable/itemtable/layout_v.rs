//! This file describes the persistent-memory layout of the
//! item table implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//! TODO: it should probably be _t because the specified layout needs
//! to be checked to make sure it matches how Rust will lay it out
//!
//! The item table has a header region with immutable metadata that is
//! written when the table is first created. This is analogous to the
//! global metadata region in each multilog.
//!
//! Metadata header (absolute offsets):
//!     bytes 0..8:     Version number of the program that created this metadata
//!     bytes 8..16:    Size of the items stored in the table
//!     bytes 16..32:   Program GUID for this program
//!     bytes 32..40:   CRC of the above 32 bytes
//!
//! The table area starts after the metadata header.
//!
//! Table entry (relative offsets):
//!     bytes 0..2:             valid bits
//!     bytes 2..10:            CRC for the entry (not including these bytes)
//!     bytes 10..<item size>:  The item stored in this entry. Size is set at
//!                             setup time but is not known at compile time.
//!

use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {
    // Constants

    // These constants describe the position of various parts of the
    // item table's layout. It's simpler than the multilog.

    pub const ABSOLUTE_POS_OF_METADATA_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM_SIZE: u64 = 8;
    pub const RELATIVE_POS_OF_NUM_KEYS: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING: u64 = 24;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 32;
    pub const LENGTH_OF_METADATA_HEADER: u64 = 48;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 48;

    // TODO: it may be more performant to skip some space and
    // start this at 256
    pub const ABSOLUTE_POS_OF_TABLE_AREA: u64 = 48;

    // This GUID was generated randomly and is meant to describe the
    // item table program, even if it has future versions.

    pub const ITEM_TABLE_PROGRAM_GUID: u128 = 0x799051C2EA1DD93680DD23065E8C9EFFu128;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const ITEM_TABLE_VERSION_NUMBER: u64 = 1;

    #[repr(C)]
    pub struct ItemTableMetadata
    {
        pub version_number: u64,
        pub item_size: u64,
        pub num_keys: u64,
        pub _padding: u64,
        pub program_guid: u128,
    }

    pub const RELATIVE_POS_OF_VALID_CDB: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_ITEM: u64 = 16;

    pub const VALID_BYTES_SIZE: u64 = 8;

    // TODO: should this be trusted?
    impl Serializable for ItemTableMetadata
    {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.version_number) +
            spec_u64_to_le_bytes(self.item_size) +
            spec_u64_to_le_bytes(self.num_keys) +
            spec_u64_to_le_bytes(self._padding) +
            spec_u128_to_le_bytes(self.program_guid)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                version_number: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_VERSION_NUMBER as int, RELATIVE_POS_OF_VERSION_NUMBER + 8)),
                item_size: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ITEM_SIZE as int, RELATIVE_POS_OF_ITEM_SIZE + 8)),
                num_keys: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NUM_KEYS as int, RELATIVE_POS_OF_NUM_KEYS + 8)),
                _padding: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING as int, RELATIVE_POS_OF_PADDING + 8)),
                program_guid: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PROGRAM_GUID as int, RELATIVE_POS_OF_PROGRAM_GUID + 16))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_guid = #[trigger] spec_u128_to_le_bytes(s.program_guid);
                let serialized_version = #[trigger] spec_u64_to_le_bytes(s.version_number);
                let serialized_item_size = #[trigger] spec_u64_to_le_bytes(s.item_size);
                let serialized_num_keys = #[trigger] spec_u64_to_le_bytes(s.num_keys);
                let serialized_padding = #[trigger] spec_u64_to_le_bytes(s._padding);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_VERSION_NUMBER as int,
                        RELATIVE_POS_OF_VERSION_NUMBER + 8
                    ) == serialized_version
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ITEM_SIZE as int,
                        RELATIVE_POS_OF_ITEM_SIZE + 8
                    ) == serialized_item_size
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_NUM_KEYS as int,
                        RELATIVE_POS_OF_NUM_KEYS + 8
                    ) == serialized_num_keys
                &&& serialized_metadata.subrange(
                    RELATIVE_POS_OF_PADDING as int,
                    RELATIVE_POS_OF_PADDING + 8
                ) == serialized_padding
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_PROGRAM_GUID as int,
                        RELATIVE_POS_OF_PROGRAM_GUID + 16
                    ) == serialized_guid
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        open spec fn spec_serialized_len() -> int
        {
            LENGTH_OF_METADATA_HEADER as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_METADATA_HEADER
        }
    }

}
