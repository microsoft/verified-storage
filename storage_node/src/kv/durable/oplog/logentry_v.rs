//! This file contains structures and methods for managing log entries
//! in the durable part of the key-value store.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//! A "log entry" is a single structure that may be appended to the log
//! that represents a single operation on the item table or list. Multiple
//! log entries may be appended as part of a single operation on the durable
//! store, and all entries that are committed with the same MultiLog `commit`
//! call should be applied atomically to the store.

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::metadata::layout_v::ListEntryMetadata;
use crate::kv::layout_v::OverallMetadata;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};

use super::oplogspec_t::AbstractPhysicalOpLogEntry;

verus! {
    // Physical log entries contain an absolute address, a size,
    // and a sequence of bytes of the specified size to copy
    // to the absolute address. The header contains the addr 
    // and len; we don't put the sequence of bytes in this 
    // struct to reduce copying in DRAM. These physical log
    // entries will be stored durably.

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    struct PhysicalLogEntryHeader {
        pub absolute_addr: u64,
        pub len: u64
    }

    impl PmCopy for PhysicalLogEntryHeader {}

    // Each concrete log entry corresponds to a logical
    // log entry type representing a logical operation on one 
    // of the components. We use these types both to 
    // represent logical operations in DRAM during execution
    // so they can be applied during commit and to abstractly
    // represent the state of the physical log.
    // Note that there are only log entries for the main table
    // and list area because recovering the item table does
    // not use logged info (although it does rely on info from
    // a recovered main table)
    #[derive(Debug)]
    pub enum LogicalOpLogEntry<L>
        where 
            L: PmCopy 
    {
        // Main table operations

        CommitMainTableEntry {
            index: u64,
        },
        InvalidateMainTableEntry {
            index: u64,
        },
        UpdateMainTableEntry {
            index: u64, 
            new_crc: u64, // we log the new CRC so we don't have to log the key and recalculate the CRC
            new_metadata: ListEntryMetadata,
        },

        // List area operations
        // // don't actually need this one! just need to use the list len to determine what 
        // // nodes have a valid next ptr and which don't
        // SetListNodeNext {
        //     node_index: u64,
        //     new_next: u64,
        // },
        UpdateListElement {
            node_index: u64,
            index_in_node: u64,
            list_element: L,
        },

        // This variant is NOT written to storage; it's used only in DRAM
        // to record which list nodes to deallocate during commit. We don't 
        // have to log it because it only represents a volatile operation 
        // (adding the nodes back to the allocator free list)
        NodeDeallocInMemory {
            old_head: u64,
            new_head: u64,
        }
    }

    // DRAM-only representation of a physical log entry, for use during recovery/
    // log installation.
    pub struct PhysicalOpLogEntry {
        pub offset: u64,
        pub absolute_addr: u64,
        pub len: u64,
        pub bytes: Vec<u8>
    }

    impl PhysicalOpLogEntry {
        pub open spec fn view(self) -> AbstractPhysicalOpLogEntry {
            AbstractPhysicalOpLogEntry {
                offset: self.offset as nat,
                absolute_addr: self.absolute_addr as nat,
                len: self.len as nat,
                bytes: self.bytes@
            }
        }

        pub open spec fn inv(self, overall_metadata: OverallMetadata) -> bool {
            &&& self.len > 0
            &&& 0 <= self.absolute_addr < self.absolute_addr + self.len < overall_metadata.region_size
            &&& ({
                ||| self.absolute_addr + self.len < overall_metadata.log_area_addr
                ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= self.absolute_addr
            })
            &&& self.len == self.bytes.len()
        }

        pub open spec fn log_inv(log: Vec<PhysicalOpLogEntry>, overall_metadata: OverallMetadata) -> bool {
            forall |i: int| 0 <= i < log.len() ==> #[trigger] log[i].inv(overall_metadata)
        }
    }

    

    // // NOTE: Verus does not support .into() so implementing the From trait is not 
    // // useful here at the moment; in the future, it would be better to have a From
    // // impl for each log entry type (except for insert list element, which needs 
    // // an additional argument?)
    // // TODO: These need postconditions
    // impl<L> OpLogEntryType<L>
    //     where L: PmCopy
    // {
    //     pub exec fn from_commit_entry(value: Box<CommitItemEntry>) -> Self {
    //         OpLogEntryType::ItemTableEntryCommit {
    //             item_index: value.item_index,
    //         }
    //     }

    //     pub exec fn to_commit_entry(&self) -> Option<CommitItemEntry> {
    //         match self {
    //             OpLogEntryType::ItemTableEntryCommit { item_index } => 
    //                 Some(CommitItemEntry {
    //                     entry_type: COMMIT_ITEM_TABLE_ENTRY,
    //                     item_index: *item_index,
    //                 }),
    //             _ => None
    //         }
    //     }

    //     pub exec fn from_invalidate_entry(value: Box<InvalidateItemEntry>) -> Self {
    //         OpLogEntryType::ItemTableEntryInvalidate { item_index: value.item_index }
    //     }

    //     pub exec fn to_invalidate_entry(&self) -> Option<InvalidateItemEntry> {
    //         match self {
    //             OpLogEntryType::ItemTableEntryInvalidate { item_index } => 
    //                 Some(InvalidateItemEntry {
    //                     entry_type: INVALIDATE_ITEM_TABLE_ENTRY,
    //                     item_index: *item_index,
    //                 }),
    //             _ => None
    //         }
    //     }

    //     pub exec fn from_append_list_node_entry(value: Box<AppendListNodeEntry>) -> Self {
    //         OpLogEntryType::AppendListNode { 
    //             metadata_index: value.metadata_index, 
    //             old_tail: value.old_tail, 
    //             new_tail: value.new_tail, 
    //         }
    //     }

    //     pub exec fn to_append_list_node_entry(&self) -> Option<AppendListNodeEntry> {
    //         match self {
    //             OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail } => 
    //                 Some(AppendListNodeEntry {
    //                     entry_type: APPEND_LIST_NODE_ENTRY,
    //                     metadata_index: *metadata_index, 
    //                     old_tail: *old_tail,
    //                     new_tail: *new_tail, 
    //                 }),
    //             _ => None,
    //         }
    //     }

    //     pub exec fn from_insert_list_element_entry(value: Box<InsertListElementEntry>, list_element: Box<L>) -> Self {
    //         OpLogEntryType::InsertListElement { 
    //             node_offset: value.node_offset, 
    //             index_in_node: value.index_in_node, 
    //             list_element: *list_element 
    //         }
    //     }

    //     pub exec fn to_insert_list_element_entry(&self) -> Option<InsertListElementEntry> {
    //         match self {
    //             OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => 
    //                 Some(InsertListElementEntry { 
    //                     entry_type: INSERT_LIST_ELEMENT_ENTRY, 
    //                     node_offset: *node_offset, 
    //                     index_in_node: *index_in_node,
    //                 }),
    //             _ => None
    //         }
    //     }

    //     pub exec fn from_commit_metadata_entry(value: Box<MetadataLogEntry>) -> Self 
    //         requires
    //             value.entry_type == COMMIT_METADATA_ENTRY
    //     {
    //         OpLogEntryType::CommitMetadataEntry { 
    //             metadata_index: value.metadata_index, 
    //         }
    //     }

    //     pub exec fn to_commit_metadata_entry(&self) -> Option<MetadataLogEntry> {
    //         match self {
    //             OpLogEntryType::CommitMetadataEntry { metadata_index } => 
    //                 Some(MetadataLogEntry { 
    //                     entry_type: COMMIT_METADATA_ENTRY, 
    //                     metadata_index: *metadata_index, 
    //                 }),
    //             _ => None,
    //         }
    //     }

    //     pub exec fn from_invalidate_metadata_entry(value: Box<MetadataLogEntry>) -> Self 
    //         requires 
    //             value.entry_type == INVALIDATE_METADATA_ENTRY
    //     {
    //         OpLogEntryType::InvalidateMetadataEntry { metadata_index: value.metadata_index }
    //     }

    //     pub exec fn to_invalidate_metadata_entry(&self) -> Option<MetadataLogEntry> {
    //         match self {
    //             OpLogEntryType::InvalidateMetadataEntry { metadata_index } => 
    //                 Some(MetadataLogEntry { entry_type: INVALIDATE_METADATA_ENTRY, metadata_index: *metadata_index }),
    //             _ => None
    //         }
    //     }

    //     pub exec fn from_update_metadata_entry(value: Box<UpdateMetadataEntry>, new_metadata: Box<ListEntryMetadata>) -> Self 
    //         requires 
    //             value.entry_type == UPDATE_METADATA_ENTRY
    //     {
    //         OpLogEntryType::UpdateMetadataEntry { metadata_index: value.metadata_index, new_crc: value.new_crc, new_metadata: *new_metadata }
    //     }

    //     pub exec fn to_update_metadata_entry(&self) -> Option<UpdateMetadataEntry> {
    //         match self {
    //             OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata, new_crc} => {
    //                 Some(UpdateMetadataEntry { entry_type: UPDATE_METADATA_ENTRY, metadata_index: *metadata_index, new_crc: *new_crc })
    //             }
    //             _ => None
    //         }
    //     }
    // }

    // // TODO: documentation
    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct CommitItemEntry {
    //     pub entry_type: u64,
    //     pub item_index: u64,
    // }

    // impl PmCopy for CommitItemEntry {}

    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct InvalidateItemEntry {
    //     pub entry_type: u64,
    //     pub item_index: u64,
    // }

    // impl PmCopy for InvalidateItemEntry {}

    // // This log entry represents an operation that appends a new list node
    // // (i.e., an array of list elements, plus a next pointer and CRC) to
    // // the list associated with the index at `metadata_index`.
    // //
    // // Writing this entry to the log should be preceded by the allocation
    // // of the new tail node (i.e., setting its next pointer to null and updating
    // // its CRC accordingly).
    // //
    // // When this log entry is replayed:
    // // 1) the old tail node of the specified list has its next pointer set
    // //    to the specified node and its CRC updated accordingly
    // // 2) the tail field and CRC of the associated list metadata structure
    // //    are updated
    // //
    // // This entry records both the old and new tail values to ensure that replaying
    // // this log entry is idempotent in cases where the list metadata struct's tail
    // // field was updated before this entry is replayed.
    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct AppendListNodeEntry {
    //     pub entry_type: u64,
    //     pub metadata_index: u64,
    //     pub old_tail: u64,
    //     pub new_tail: u64,
    // }

    // impl PmCopy for AppendListNodeEntry {}

    // // This log entry represents an operation that writes a new list element
    // // to the specified index in the specified ULL node. Note that the index
    // // refers to the index in the list node's array, NOT the logical list
    // // index that this operation updates.
    // //
    // // This type of log entry must contain the new list element to write, as
    // // the insertion may update a live list element, which is a commiting update.
    // // To avoid extra in-memory copying of the list element, we do not include
    // // it directly in this structure.
    // //
    // // When this log entry is replayed:
    // // 1) the list element immediately following it in the log is copied to
    // //    the specified index in the specified list node.
    // //
    // // Note that this log entry type does not need to be used for appends.
    // // Appending a new list element is a tentative update, as it is modifying
    // // a list element outside the current bounds of the list, so it doesn't have
    // // to be logged. This entry type only needs to be used for in-place updates
    // // of in-bounds indices.
    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct InsertListElementEntry {
    //     pub entry_type: u64,
    //     pub node_offset: u64,
    //     pub index_in_node: u64,
    // }

    // impl PmCopy for InsertListElementEntry {}

    // // represents commit and invalidate metadata entries.
    // // update entries record a CRC and use a different log entry type
    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct MetadataLogEntry {
    //     pub entry_type: u64,
    //     pub metadata_index: u64,
    // }

    // impl PmCopy for MetadataLogEntry {}

    // #[repr(C)]
    // #[derive(PmSized, PmSafe, Copy, Clone)]
    // pub struct UpdateMetadataEntry {
    //     pub entry_type: u64,
    //     pub metadata_index: u64,
    //     pub new_crc: u64,
    // }

    // impl PmCopy for UpdateMetadataEntry {}
}
