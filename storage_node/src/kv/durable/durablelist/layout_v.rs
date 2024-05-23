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
use crate::kv::durable::metadata::layout_v::*;


verus! {
    // These constants describe the position of various parts
    // of the durable list structures on persistent memory.
    // Note that the durable list uses multiple persistent
    // memory regions.

    // Header of the node region. Contains metadata to identify the
    // region and determine the number of nodes.
    pub const ABSOLUTE_POS_OF_LIST_REGION_HEADER: u64 = 0;
    pub const RELATIVE_POS_OF_NUM_NODES: u64 = 0;
    pub const RELATIVE_POS_OF_LIST_REGION_LEN: u64 = 8;
    pub const RELATIVE_POS_OF_LIST_VERSION_NUMBER: u64 = 16;
    pub const RELATIVE_POS_OF_LIST_REGION_HEADER_PADDING: u64 = 24;
    pub const RELATIVE_POS_OF_LIST_PROGRAM_GUID: u64 = 32;
    pub const LENGTH_OF_LIST_REGION_HEADER: u64 = 48;
    pub const ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC: u64 = 48;
    pub const ABSOLUTE_POS_OF_LIST_REGION_NODE_START: u64 = 56;

    pub const DURABLE_LIST_REGION_VERSION_NUMBER: u64 = 1;

    pub const DURABLE_LIST_REGION_PROGRAM_GUID: u128 = 0x02d7708c1acffbf895faa6728ba5e037u128;

    #[repr(C)]
    pub struct ListRegionHeader {
        pub num_nodes: u64,
        pub length: u64,
        pub version_number: u64,
        pub _padding0: u64,
        pub program_guid: u128,
    }

    impl Serializable for ListRegionHeader {
        closed spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.num_nodes) +
            spec_u64_to_le_bytes(self.length) + 
            spec_u64_to_le_bytes(self.version_number) +
            spec_u64_to_le_bytes(self._padding0) + 
            spec_u128_to_le_bytes(self.program_guid)
        }

        closed spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                num_nodes: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NUM_NODES as int, RELATIVE_POS_OF_NUM_NODES + 8)),
                length: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_REGION_LEN as int, RELATIVE_POS_OF_LIST_REGION_LEN + 8)),
                version_number: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_VERSION_NUMBER as int, RELATIVE_POS_OF_LIST_VERSION_NUMBER + 8)),
                _padding0: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_REGION_HEADER_PADDING as int, RELATIVE_POS_OF_LIST_REGION_HEADER_PADDING + 8)),
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
                let serialized_len = #[trigger] spec_u64_to_le_bytes(s.length);
                let serialized_num_nodes = #[trigger] spec_u64_to_le_bytes(s.num_nodes);
                let serialized_padding = #[trigger] spec_u64_to_le_bytes(s._padding0);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_NUM_NODES as int,
                        RELATIVE_POS_OF_NUM_NODES + 8
                    ) == serialized_num_nodes
                &&& serialized_metadata.subrange(
                            RELATIVE_POS_OF_LIST_REGION_LEN as int,
                            RELATIVE_POS_OF_LIST_REGION_LEN + 8
                    ) == serialized_len
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LIST_VERSION_NUMBER as int,
                        RELATIVE_POS_OF_LIST_VERSION_NUMBER + 8
                    ) == serialized_version
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LIST_REGION_HEADER_PADDING as int,
                        RELATIVE_POS_OF_LIST_REGION_HEADER_PADDING + 8
                    ) == serialized_padding
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

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
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

    // `mem` is the full list node region, not just the bytes associated with this node
    pub open spec fn parse_list_node<L>(
        idx: int, 
        metadata_header: MetadataTableHeader, 
        mem: Seq<u8>
    ) -> Option<(u64, Seq<Seq<u8>>)>
        where 
            L: Serializable 
    {
        let list_entry_size = L::spec_serialized_len() + CRC_SIZE;
        // let node_size = (mem.len() - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / metadata_header.num_nodes;
        // let elements_per_node = (node_size - LENGTH_OF_LIST_NODE_HEADER) / list_entry_size;
        // check that the metadata in the header makes sense/is valid
        // We should have already checked this when parsing the metadata table, but do it again here to be safe
        if {
            ||| metadata_header.program_guid != DURABLE_LIST_REGION_PROGRAM_GUID 
            ||| metadata_header.version_number != 1
            ||| list_entry_size != metadata_header.element_size
            ||| mem.len() < LENGTH_OF_LIST_REGION_HEADER
        } {
            None
        } else {
            let node_region_header_bytes = mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER + LENGTH_OF_LIST_REGION_HEADER);
            let node_region_header = ListRegionHeader::spec_deserialize(node_region_header_bytes);
            let node_region_header_crc = mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC + 8);
            let node_region_crc = u64::spec_deserialize(node_region_header_crc);
            // check that node region header is valid
            if node_region_crc != node_region_header.spec_crc() {
                None
            } else {
                let node_size = (mem.len() - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / node_region_header.num_nodes as int;
                let elements_per_node = (node_size - LENGTH_OF_LIST_NODE_HEADER) / list_entry_size;
                if {
                    ||| mem.len() < node_region_header.length 
                    ||| node_region_header.version_number != 1
                    ||| node_region_header.program_guid != DURABLE_LIST_REGION_PROGRAM_GUID
                } {
                    None 
                } else {
                    // now that we know the node region is valid, parse the desired node
                    let node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + idx * node_size;
                    let node_bytes = mem.subrange(node_offset as int, node_offset + node_size);
                    let next_pointer_bytes = node_bytes.subrange(RELATIVE_POS_OF_NEXT_POINTER as int, RELATIVE_POS_OF_NEXT_POINTER + 8);
                    let next_crc_bytes = node_bytes.subrange(RELATIVE_POS_OF_LIST_NODE_CRC as int, RELATIVE_POS_OF_LIST_NODE_CRC + 8);
                    // check the next pointer CRC
                    let next_pointer = u64::spec_deserialize(next_pointer_bytes);
                    let crc = u64::spec_deserialize(next_crc_bytes);
                    if crc != next_pointer.spec_crc() {
                        None 
                    } else {
                        // Note: we return the full bytes of each list entry, including CRC, and do not check whether 
                        // the element matches the CRC. Some CRCs may be incorrect until we replay the log. We also 
                        // return all list entries and let the caller decide which ones they are going to keep
                        Some((
                            next_pointer,
                            Seq::new(
                                elements_per_node as nat,
                                |i: int| node_bytes.subrange(
                                    RELATIVE_POS_OF_LIST_CONTENTS_AREA + i * list_entry_size,
                                    RELATIVE_POS_OF_LIST_CONTENTS_AREA + i * list_entry_size + list_entry_size
                                )
                            )
                        ))
                    }
                }
            }
        }
    }

    // per-element relative offsets. The CRC comes before the list element because we do not 
    // know the size of the list element here
    pub const RELATIVE_POS_OF_LIST_ELEMENT_CRC: u64 = 0;
    pub const RELATIVE_POS_OF_LIST_ELEMENT: u64 = 8;

}
