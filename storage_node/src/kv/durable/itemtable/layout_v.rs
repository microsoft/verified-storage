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

use super::itemtablespec_t::DurableItemTableView;
use super::itemtablespec_t::DurableItemTableViewEntry;

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
        pub item_size: u64, // just I::serialized_len() -- does not include key, CRC, CDB
        pub num_keys: u64,
        pub _padding: u64,
        pub program_guid: u128,
    }

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

    pub const RELATIVE_POS_OF_VALID_CDB: u64 = 0;
    pub const RELATIVE_POS_OF_ITEM_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_ITEM: u64 = 16;

    // TODO: This should be a closed method of the item table view type?
    // TODO: maybe apply log to bytes BEFORE doing this?
    pub open spec fn parse_item_table<I, K, E>(metadata_header: ItemTableMetadata, mem: Seq<u8>) -> Option<DurableItemTableView<I, K, E>>
        where 
            I: Serializable,
            K: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        // Check that the header is valid and the memory is the correct size.
        // We probably already did these checks when we parsed the metadata header, but
        // do them again here just in case
        if {
            ||| metadata_header.version_number != 1
            ||| metadata_header.program_guid != ITEM_TABLE_PROGRAM_GUID
            ||| metadata_header.item_size != I::spec_serialized_len()
            ||| mem.len() < ABSOLUTE_POS_OF_TABLE_AREA + (metadata_header.item_size + CRC_SIZE + CDB_SIZE) * metadata_header.num_keys 
        } { 
            None
        } else {
            let table_area = mem.subrange(ABSOLUTE_POS_OF_TABLE_AREA as int, mem.len() as int);
            let item_entry_size = metadata_header.item_size + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
            let item_table_view = Seq::new(
                metadata_header.num_keys as nat,
                |i: int| {
                    // the offset of the key depends on the offset of the item, so we don't have a constant for it
                    let relative_key_offset = RELATIVE_POS_OF_ITEM + I::spec_serialized_len();
                    let bytes = table_area.subrange(i * item_entry_size, i * item_entry_size + item_entry_size);
                    let cdb_bytes = bytes.subrange(RELATIVE_POS_OF_VALID_CDB as int, RELATIVE_POS_OF_VALID_CDB + CDB_SIZE);
                    let crc_bytes = bytes.subrange(RELATIVE_POS_OF_ITEM_CRC as int, RELATIVE_POS_OF_ITEM_CRC + 8);
                    let item_bytes = bytes.subrange(RELATIVE_POS_OF_ITEM as int, RELATIVE_POS_OF_ITEM + I::spec_serialized_len());
                    let key_bytes = bytes.subrange(relative_key_offset, relative_key_offset + K::spec_serialized_len());
                    
                    let cdb = u64::spec_deserialize(cdb_bytes);
                    let crc = u64::spec_deserialize(crc_bytes);
                    let item = I::spec_deserialize(item_bytes);
                    let key = K::spec_deserialize(key_bytes);
                    
                    DurableItemTableViewEntry::new(cdb, crc, item, key)
                }
            );
            // Finally, return None if any of the CRCs are invalid
            // TODO: is this a reasonable way to check this, or is there a better way to do it?
            // TODO: skip invalid entries
            if !(forall |i: int| #![auto] 0 <= i < item_table_view.len() ==> 
                item_table_view[i].get_crc() != spec_crc_u64(item_table_view[i].get_item().spec_serialize() + item_table_view[i].get_key().spec_serialize())) 
            {
                None 
            } else {
                Some(DurableItemTableView::new(item_table_view))
            }
        }
    }
}
