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
use crate::pmem::pmcopy_t::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::pmem::traits_t::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};


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
    pub const ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC: u64 = 48;
    pub const ABSOLUTE_POS_OF_LIST_REGION_NODE_START: u64 = 56;

    pub const DURABLE_LIST_REGION_VERSION_NUMBER: u64 = 1;

    pub const DURABLE_LIST_REGION_PROGRAM_GUID: u128 = 0x02d7708c1acffbf895faa6728ba5e037u128;

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct ListRegionHeader {
        pub num_nodes: u64,
        pub length: u64,
        pub version_number: u64,
        pub _padding0: u64,
        pub program_guid: u128,
    }

    impl PmCopy for ListRegionHeader {}

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

    // `mem` is the full list node region, not just the bytes associated with this node
    pub open spec fn parse_list_node<L>(
        idx: int, 
        mem: Seq<u8>,
        list_node_size: u64,
        num_list_entries_per_node: u32,
    ) -> Option<(u64, Seq<Seq<u8>>)>
        where 
            L: PmCopy 
    {
        let list_entry_size = L::spec_size_of() + u64::spec_size_of();
        // We should have already checked this when parsing the metadata table, but do it again here to be safe
        if mem.len() < ListRegionHeader::spec_size_of() {
            None
        } else {
            let node_region_header_bytes = mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER + u64::spec_size_of() + u64::spec_size_of());
            let node_region_header = ListRegionHeader::spec_from_bytes(node_region_header_bytes);
            let node_region_header_crc = mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC + u64::spec_size_of());
            let node_region_crc = u64::spec_from_bytes(node_region_header_crc);
            // check that node region header is valid
            if node_region_crc != node_region_header.spec_crc() {
                None
            } else {
                let node_size = (mem.len() - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / node_region_header.num_nodes as int;
                let elements_per_node = (node_size - (u64::spec_size_of() + u64::spec_size_of())) / list_entry_size as int;
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
                    let next_pointer = u64::spec_from_bytes(next_pointer_bytes);
                    let crc = u64::spec_from_bytes(next_crc_bytes);
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
