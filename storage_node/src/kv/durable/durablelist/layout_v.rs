//! This file describes the persistent-memory layout of the
//! durable list implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//!
//!

use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

use super::durablelistspec_t::DurableListElementView;

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
    pub const RELATIVE_POS_OF_NUM_KEYS: u64 = 8;
    pub const RELATIVE_POS_OF_VERSION_NUMBER: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING: u64 = 24;
    pub const RELATIVE_POS_OF_PROGRAM_GUID: u64 = 32;
    pub const LENGTH_OF_METADATA_HEADER: u64 = 48;
    pub const ABSOLUTE_POS_OF_HEADER_CRC: u64 = 48;

    pub const ABSOLUTE_POS_OF_METADATA_TABLE: u64 = 56;

    // The current version number, and the only one whose contents
    // this program can read, is the following:
    pub const LIST_METADATA_VERSION_NUMBER: u64 = 1;

    // This GUID was generated randomly and is meant to describe the
    // durable list program, even if it has future versions.
    pub const DURABLE_LIST_METADATA_TABLE_PROGRAM_GUID: u128 = 0xC357BD8AA950BDA76345F1DCEC7DBF3Fu128;

    // TODO: we use node size in some places and elements per node in others
    // should probably standardize this
    #[repr(C)]
    pub struct GlobalListMetadata
    {
        pub element_size: u32, // NOTE: this includes the CRC of each element
        pub node_size: u32,
        pub num_keys: u64,
        pub version_number: u64,
        pub _padding: u64,
        pub program_guid: u128,
    }

    // TODO: should this be trusted?
    impl Serializable for GlobalListMetadata
    {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u32_to_le_bytes(self.element_size) +
            spec_u32_to_le_bytes(self.node_size) +
            spec_u64_to_le_bytes(self.num_keys) +
            spec_u64_to_le_bytes(self.version_number) +
            spec_u64_to_le_bytes(self._padding) +
            spec_u128_to_le_bytes(self.program_guid)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self {
            Self {
                element_size: spec_u32_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ELEMENT_SIZE as int, RELATIVE_POS_OF_ELEMENT_SIZE + 4)),
                node_size: spec_u32_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NODE_SIZE as int, RELATIVE_POS_OF_NODE_SIZE + 4)),
                num_keys: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NUM_KEYS as int, RELATIVE_POS_OF_NUM_KEYS + 8)),
                version_number: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_VERSION_NUMBER as int, RELATIVE_POS_OF_VERSION_NUMBER + 8)),
                _padding: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING as int, RELATIVE_POS_OF_PADDING + 8)),
                program_guid: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PROGRAM_GUID as int, RELATIVE_POS_OF_PROGRAM_GUID + 16))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_element_size = #[trigger] spec_u32_to_le_bytes(s.element_size);
                let serialized_node_size = #[trigger] spec_u32_to_le_bytes(s.node_size);
                let serialized_num_keys = #[trigger] spec_u64_to_le_bytes(s.num_keys);
                let serialized_version_number = #[trigger] spec_u64_to_le_bytes(s.version_number);
                let serialized_padding = #[trigger] spec_u64_to_le_bytes(s._padding);
                let serialized_program_guid = #[trigger] spec_u128_to_le_bytes(s.program_guid);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ELEMENT_SIZE as int,
                        RELATIVE_POS_OF_ELEMENT_SIZE + 4
                    ) == serialized_element_size
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_NODE_SIZE as int,
                        RELATIVE_POS_OF_NODE_SIZE + 4
                    ) == serialized_node_size
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_NUM_KEYS as int,
                        RELATIVE_POS_OF_NUM_KEYS + 8
                    ) == serialized_num_keys
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_VERSION_NUMBER as int,
                        RELATIVE_POS_OF_VERSION_NUMBER + 8
                    ) == serialized_version_number
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_PADDING as int,
                        RELATIVE_POS_OF_PADDING + 8
                    ) == serialized_padding
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_PROGRAM_GUID as int,
                        RELATIVE_POS_OF_PROGRAM_GUID + 16
                    ) == serialized_program_guid
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u32_to_from_le_bytes();
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

    // Per-entry relative offsets for list entry metadata
    // The list metadata region is an array of list entry metadata
    // structures, each of which contains metadata about the list
    // associated with a given key of type K. K must be Sized,
    // but we need to be generic over any K, so the key is the last
    // field of the structure to avoid layout weirdness.
    // This means it is easiest to put the CRC *before* the corresponding
    // ListEntryMetadata structure, so the constants here are a bit weird

    pub const RELATIVE_POS_OF_VALID_CDB: u64 = 0;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_ENTRY_METADATA: u64 = 16; // pos of the ListEntryMetadata structure to its slot's offset
    pub const RELATIVE_POS_OF_ENTRY_METADATA_HEAD: u64 = 0; // pos of head field relative to ListEntryMetadata structure pos
    pub const RELATIVE_POS_OF_ENTRY_METADATA_TAIL: u64 = 8;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_LENGTH: u64 = 16;
    pub const RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET: u64 = 24;
    pub const RELATIVE_POS_OF_ENTRY_KEY: u64 = 32;
    pub const LENGTH_OF_ENTRY_METADATA_MINUS_KEY: u64 = 32;

    #[repr(C)]
    pub struct ListEntryMetadata
    {
        head: u64,
        tail: u64,
        length: u64,
        first_entry_offset: u64, // offset of the first live entry in the head node
    }

    impl ListEntryMetadata {
        pub fn get_head(&self) -> (out: u64) 
            ensures
                out == self.spec_head()
        {
            self.head
        }

        pub closed spec fn spec_head(self) -> u64 
        {
            self.head
        }

        pub closed spec fn spec_len(self) -> u64 
        {
            self.length
        }
    }

    pub open spec(checked) fn parse_metadata_entry<K>(bytes: Seq<u8>) -> Option<(K, ListEntryMetadata)>
        where 
            K: Serializable,
        recommends
            bytes.len() == LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CDB_SIZE + CRC_SIZE + K::spec_serialized_len(),
            RELATIVE_POS_OF_VALID_CDB + CDB_SIZE <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA_CRC + CRC_SIZE <= bytes.len(),
            RELATIVE_POS_OF_ENTRY_METADATA + LENGTH_OF_ENTRY_METADATA_MINUS_KEY <= bytes.len(),
    {
        let cdb = spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_VALID_CDB as int, RELATIVE_POS_OF_VALID_CDB + CDB_SIZE));
        let crc = spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_CRC as int, RELATIVE_POS_OF_ENTRY_METADATA_CRC + CRC_SIZE));
        let metadata_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA as int, RELATIVE_POS_OF_ENTRY_METADATA + LENGTH_OF_ENTRY_METADATA_MINUS_KEY);
        let key_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_KEY as int, RELATIVE_POS_OF_ENTRY_KEY + K::spec_serialized_len());
        let metadata = ListEntryMetadata::spec_deserialize(metadata_bytes);
        let key = K::spec_deserialize(key_bytes);
    
        if cdb == CDB_FALSE {
            None 
        } else {
            // If the CRC does not match the contents, it's not a valid entry
            if crc != spec_crc_u64(metadata_bytes + key_bytes) {
                None 
            } else {
                Some((key, metadata))
            }
        }
    }

    // We parse the metadata table into a Seq of `DurableItemTableViewEntry`s because the metadata table is essentially an item table.
    // We don't return a `DurableItemTableView` so that we can recurse over the sequence of entries without adding methods to that view 
    // and because the metadata table has a different header structure.
    pub open spec fn parse_metadata_table<K>(header: GlobalListMetadata, mem: Seq<u8>) -> Option<Seq<DurableItemTableViewEntry<ListEntryMetadata, K>>>
        where 
            K: Serializable + std::fmt::Debug,
    {
        let table_entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
        // check that the metadata in the header makes sense/is valid
        if {
            ||| header.program_guid != DURABLE_LIST_REGION_PROGRAM_GUID 
            ||| header.version_number != 1
            ||| mem.len() < ABSOLUTE_POS_OF_METADATA_TABLE + table_entry_slot_size * header.num_keys
        } {
            None
        } else {
            let table_area = mem.subrange(ABSOLUTE_POS_OF_METADATA_TABLE as int, mem.len() as int);
            let table_view = Seq::new(
                header.num_keys as nat,
                |i: int| {
                    let bytes = table_area.subrange(i * table_entry_slot_size, i * table_entry_slot_size + table_entry_slot_size);
                    let cdb_bytes = bytes.subrange(RELATIVE_POS_OF_VALID_CDB as int, RELATIVE_POS_OF_VALID_CDB + CDB_SIZE);
                    let crc_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_CRC as int, RELATIVE_POS_OF_ENTRY_METADATA_CRC + CRC_SIZE);
                    let entry_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA as int, RELATIVE_POS_OF_ENTRY_METADATA + LENGTH_OF_ENTRY_METADATA_MINUS_KEY);
                    let key_bytes = bytes.subrange(RELATIVE_POS_OF_ENTRY_KEY as int, RELATIVE_POS_OF_ENTRY_KEY + K::spec_serialized_len());

                    let cdb = u64::spec_deserialize(cdb_bytes);
                    let crc = u64::spec_deserialize(crc_bytes);
                    let entry = ListEntryMetadata::spec_deserialize(entry_bytes);
                    let key = K::spec_deserialize(key_bytes);

                    // we can't check CRCs in this closure, since its return value is only used to construct the Seq

                    DurableItemTableViewEntry::new(cdb, crc, entry, key)
                }
            );
            // Finally, return None if any of the CRCs are invalid
            // TODO: is this a reasonable way to check this, or is there a better way to do it
            if !(forall |i: int| 0 <= i < table_view.len() ==> table_view[i].get_crc() == spec_crc_u64(table_view[i].get_item().spec_serialize() + table_view[i].get_key().spec_serialize())) {
                None 
            } else {
                Some(table_view)
            }
        }
    }


    impl Serializable for ListEntryMetadata
    {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.head) +
            spec_u64_to_le_bytes(self.tail) +
            spec_u64_to_le_bytes(self.length) +
            spec_u64_to_le_bytes(self.first_entry_offset)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                head: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_HEAD as int, RELATIVE_POS_OF_ENTRY_METADATA_HEAD + 8)),
                tail: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_TAIL as int, RELATIVE_POS_OF_ENTRY_METADATA_TAIL + 8)),
                length: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_LENGTH as int, RELATIVE_POS_OF_ENTRY_METADATA_LENGTH + 8)),
                first_entry_offset: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET as int, RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_head = #[trigger] spec_u64_to_le_bytes(s.head);
                let serialized_tail = #[trigger] spec_u64_to_le_bytes(s.tail);
                let serialized_length = #[trigger] spec_u64_to_le_bytes(s.length);
                let serialized_first_entry_offset = #[trigger] spec_u64_to_le_bytes(s.first_entry_offset);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ENTRY_METADATA_HEAD as int,
                        RELATIVE_POS_OF_ENTRY_METADATA_HEAD + 8
                    ) == serialized_head
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ENTRY_METADATA_TAIL as int,
                        RELATIVE_POS_OF_ENTRY_METADATA_TAIL + 8
                    ) == serialized_tail
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ENTRY_METADATA_LENGTH as int,
                        RELATIVE_POS_OF_ENTRY_METADATA_LENGTH + 8
                    ) == serialized_length
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET as int,
                        RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET + 8
                    ) == serialized_first_entry_offset
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
        }

        open spec fn spec_serialized_len() -> int
        {
            LENGTH_OF_ENTRY_METADATA_MINUS_KEY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_ENTRY_METADATA_MINUS_KEY
        }
    }

    // Header of the node region. Contains metadata to identify the
    // region and determine the number of nodes.
    pub const ABSOLUTE_POS_OF_LIST_REGION_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_NUM_NODES: u64 = 0;
    pub const RELATIVE_POS_OF_LIST_VERSION_NUMBER: u64 = 8;
    pub const RELATIVE_POS_OF_LIST_PROGRAM_GUID: u64 = 16;
    pub const LENGTH_OF_LIST_REGION_HEADER: u64 = 32;
    pub const ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC: u64 = 32;
    pub const ABSOLUTE_POS_OF_LIST_REGION_NODE_START: u64 = 40;

    pub const DURABLE_LIST_REGION_VERSION_NUMBER: u64 = 1;

    pub const DURABLE_LIST_REGION_PROGRAM_GUID: u128 = 0x02d7708c1acffbf895faa6728ba5e037u128;

    #[repr(C)]
    pub struct ListRegionHeader {
        pub num_nodes: u64,
        pub version_number: u64,
        pub program_guid: u128,
    }

    impl Serializable for ListRegionHeader {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.num_nodes) +
            spec_u64_to_le_bytes(self.version_number) +
            spec_u128_to_le_bytes(self.program_guid)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                num_nodes: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NUM_NODES as int, RELATIVE_POS_OF_NUM_NODES + 8)),
                version_number: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_VERSION_NUMBER as int, RELATIVE_POS_OF_LIST_VERSION_NUMBER + 8)),
                program_guid: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_PROGRAM_GUID as int, RELATIVE_POS_OF_LIST_PROGRAM_GUID + 16))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_guid = #[trigger] spec_u128_to_le_bytes(s.program_guid);
                let serialized_version = #[trigger] spec_u64_to_le_bytes(s.version_number);
                let serialized_num_nodes = #[trigger] spec_u64_to_le_bytes(s.num_nodes);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LIST_VERSION_NUMBER as int,
                        RELATIVE_POS_OF_LIST_VERSION_NUMBER + 8
                    ) == serialized_version
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_NUM_NODES as int,
                        RELATIVE_POS_OF_NUM_NODES + 8
                    ) == serialized_num_nodes
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LIST_PROGRAM_GUID as int,
                        RELATIVE_POS_OF_LIST_PROGRAM_GUID + 16
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
            LENGTH_OF_LIST_REGION_HEADER as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LIST_REGION_HEADER
        }
    }

    // Per-node relative offsets for unrolled linked list nodes
    // Most list metadata is stored in the ListEntryMetadata structure,
    // so nodes only need to have a next pointer and a CRC for that
    // pointer. Since it's only 2 fields and one is a CRC, there is
    // no struct associated with the node metadata.
    //
    // Since the next pointers are structured as offsets into an array of
    // notes, 0 may be a valid next pointer. So, to indicate that a node
    // is the tail of its list, its next pointer will point to *itself*
    // rather than being set to 0.
    pub const RELATIVE_POS_OF_NEXT_POINTER: u64 = 0;
    pub const RELATIVE_POS_OF_LIST_NODE_CRC: u64 = 8;
    pub const RELATIVE_POS_OF_LIST_CONTENTS_AREA: u64 = 16;
    pub const LENGTH_OF_LIST_NODE_HEADER: u64 = 16;

    // pub open spec fn parse_list<K>(
    //     key: K,
    //     metadata: ListEntryMetadata,
    //     list_region_mem: Seq<u8>
    // ) -> Seq<DurableListElementView<L>> 
    // {
        
    // }

}
