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
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};

verus! {
    /*
     * Item table entry types
     * - Validate item (item index, item CRC)
     * - Invalidate item (item index)
     * - Delete item (item index)
     *
     * List entry types
     * - Update list entry (PM offset, new entry contents)
     * - Append list entry to existing node (node offset, new num entries)
     * - Append node to list (tail node offset, new node offset)
     * - Set new head node (PM offset, new node header)
     * - Delete x nodes (PM offset of first node to delete)
     */

    // It's safe to use 0 as a type -- we won't mistake empty space
    // for a valid entry -- because the log guarantees that we
    // only read entries that have been appended to it and no
    // old or garbage data.

    // These don't need to be u64s, but using 8 bytes makes it easier to
    // structure the log entries with a predicable layout

    pub const COMMIT_ITEM_TABLE_ENTRY: u64 = 0;
    pub const INVALIDATE_ITEM_TABLE_ENTRY: u64 = 1;
    pub const APPEND_LIST_NODE_ENTRY: u64 = 2;
    pub const INSERT_LIST_ELEMENT_ENTRY: u64 = 3;
    // pub const UPDATE_LIST_LEN_ENTRY: u64 = 4; // for new (appended) or in-place element updates
    // pub const TRIM_LIST_METADATA_UPDATE_ENTRY: u64 = 5; // updates head, len, and start index during trim
    pub const COMMIT_METADATA_ENTRY: u64 = 4;
    pub const INVALIDATE_METADATA_ENTRY: u64 = 5;
    pub const UPDATE_METADATA_ENTRY: u64 = 6;

    // layout constants for concrete log entry types
    // the entry type is first in all entries
    pub const RELATIVE_POS_OF_LOG_ENTRY_TYPE: u64 = 0;


    // commit item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM: u64 = 8;
    pub const RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM: u64 = 16;
    pub const RELATIVE_POS_OF_CRC_COMMIT_ITEM: u64 = 24;

    // invalidate item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM: u64 = 8;

    // append list node entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE: u64 = 8;
    pub const RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE: u64 = 16;
    pub const RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE: u64 = 24;
    pub const RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE: u64 = 32;

    // insert list element entry
    pub const RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT: u64 = 8;
    pub const RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT: u64 = 16;

    // commit metadata entry 
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA: u64 = 8;
    pub const RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA: u64 = 16;

    // delete metadata entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA: u64 = 8;

    // Enum representing different op log entry types.
    // The concrete types we write to the log are not enums so that we have more control 
    // over layout; this enum is used represent log entries in ghost code and in DRAM 
    // during log replay
    #[derive(Debug)]
    pub enum OpLogEntryType<L>
        where
            L: PmCopy
    {
        ItemTableEntryCommit { 
            item_index: u64,
        },
        ItemTableEntryInvalidate { item_index: u64 },
        AppendListNode {
            metadata_index: u64,
            old_tail: u64,
            new_tail: u64,
        },
        InsertListElement {
            node_offset: u64,
            index_in_node: u64,
            list_element: L
        },
        CommitMetadataEntry {
            metadata_index: u64,
        },
        InvalidateMetadataEntry {
            metadata_index: u64,
        },
        UpdateMetadataEntry {
            metadata_index: u64,
            new_crc: u64, // logged so that we don't have to log the key
            new_metadata: ListEntryMetadata,
        },
        // This enum is NOT written to the durable log -- it's just a marker in 
        // the in-memory log entry list to help us determine which list nodes
        // should be deallocated during commit.
        NodeDeallocInMemory {
            old_head: u64,
            new_head: u64,
        }
    }

    // NOTE: Verus does not support .into() so implementing the From trait is not 
    // useful here at the moment; in the future, it would be better to have a From
    // impl for each log entry type (except for insert list element, which needs 
    // an additional argument?)
    // TODO: These need postconditions
    impl<L> OpLogEntryType<L>
        where L: PmCopy
    {
        pub exec fn from_commit_entry(value: Box<CommitItemEntry>) -> Self {
            OpLogEntryType::ItemTableEntryCommit {
                item_index: value.item_index,
            }
        }

        pub exec fn to_commit_entry(&self) -> Option<CommitItemEntry> {
            match self {
                OpLogEntryType::ItemTableEntryCommit { item_index } => 
                    Some(CommitItemEntry {
                        entry_type: COMMIT_ITEM_TABLE_ENTRY,
                        item_index: *item_index,
                    }),
                _ => None
            }
        }

        pub exec fn from_invalidate_entry(value: Box<InvalidateItemEntry>) -> Self {
            OpLogEntryType::ItemTableEntryInvalidate { item_index: value.item_index }
        }

        pub exec fn to_invalidate_entry(&self) -> Option<InvalidateItemEntry> {
            match self {
                OpLogEntryType::ItemTableEntryInvalidate { item_index } => 
                    Some(InvalidateItemEntry {
                        entry_type: INVALIDATE_ITEM_TABLE_ENTRY,
                        item_index: *item_index,
                    }),
                _ => None
            }
        }

        pub exec fn from_append_list_node_entry(value: Box<AppendListNodeEntry>) -> Self {
            OpLogEntryType::AppendListNode { 
                metadata_index: value.metadata_index, 
                old_tail: value.old_tail, 
                new_tail: value.new_tail, 
            }
        }

        pub exec fn to_append_list_node_entry(&self) -> Option<AppendListNodeEntry> {
            match self {
                OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail } => 
                    Some(AppendListNodeEntry {
                        entry_type: APPEND_LIST_NODE_ENTRY,
                        metadata_index: *metadata_index, 
                        old_tail: *old_tail,
                        new_tail: *new_tail, 
                    }),
                _ => None,
            }
        }

        pub exec fn from_insert_list_element_entry(value: Box<InsertListElementEntry>, list_element: Box<L>) -> Self {
            OpLogEntryType::InsertListElement { 
                node_offset: value.node_offset, 
                index_in_node: value.index_in_node, 
                list_element: *list_element 
            }
        }

        pub exec fn to_insert_list_element_entry(&self) -> Option<InsertListElementEntry> {
            match self {
                OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => 
                    Some(InsertListElementEntry { 
                        entry_type: INSERT_LIST_ELEMENT_ENTRY, 
                        node_offset: *node_offset, 
                        index_in_node: *index_in_node,
                    }),
                _ => None
            }
        }

        pub exec fn from_commit_metadata_entry(value: Box<MetadataLogEntry>) -> Self 
            requires
                value.entry_type == COMMIT_METADATA_ENTRY
        {
            OpLogEntryType::CommitMetadataEntry { 
                metadata_index: value.metadata_index, 
            }
        }

        pub exec fn to_commit_metadata_entry(&self) -> Option<MetadataLogEntry> {
            match self {
                OpLogEntryType::CommitMetadataEntry { metadata_index } => 
                    Some(MetadataLogEntry { 
                        entry_type: COMMIT_METADATA_ENTRY, 
                        metadata_index: *metadata_index, 
                    }),
                _ => None,
            }
        }

        pub exec fn from_invalidate_metadata_entry(value: Box<MetadataLogEntry>) -> Self 
            requires 
                value.entry_type == INVALIDATE_METADATA_ENTRY
        {
            OpLogEntryType::InvalidateMetadataEntry { metadata_index: value.metadata_index }
        }

        pub exec fn to_invalidate_metadata_entry(&self) -> Option<MetadataLogEntry> {
            match self {
                OpLogEntryType::InvalidateMetadataEntry { metadata_index } => 
                    Some(MetadataLogEntry { entry_type: INVALIDATE_METADATA_ENTRY, metadata_index: *metadata_index }),
                _ => None
            }
        }

        pub exec fn from_update_metadata_entry(value: Box<UpdateMetadataEntry>, new_metadata: Box<ListEntryMetadata>) -> Self 
            requires 
                value.entry_type == UPDATE_METADATA_ENTRY
        {
            OpLogEntryType::UpdateMetadataEntry { metadata_index: value.metadata_index, new_crc: value.new_crc, new_metadata: *new_metadata }
        }

        pub exec fn to_update_metadata_entry(&self) -> Option<UpdateMetadataEntry> {
            match self {
                OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata, new_crc} => {
                    Some(UpdateMetadataEntry { entry_type: UPDATE_METADATA_ENTRY, metadata_index: *metadata_index, new_crc: *new_crc })
                }
                _ => None
            }
        }
    }

    // TODO: documentation
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct CommitItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
    }

    impl PmCopy for CommitItemEntry {}

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct InvalidateItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
    }

    impl PmCopy for InvalidateItemEntry {}

    // This log entry represents an operation that appends a new list node
    // (i.e., an array of list elements, plus a next pointer and CRC) to
    // the list associated with the index at `metadata_index`.
    //
    // Writing this entry to the log should be preceded by the allocation
    // of the new tail node (i.e., setting its next pointer to null and updating
    // its CRC accordingly).
    //
    // When this log entry is replayed:
    // 1) the old tail node of the specified list has its next pointer set
    //    to the specified node and its CRC updated accordingly
    // 2) the tail field and CRC of the associated list metadata structure
    //    are updated
    //
    // This entry records both the old and new tail values to ensure that replaying
    // this log entry is idempotent in cases where the list metadata struct's tail
    // field was updated before this entry is replayed.
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct AppendListNodeEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub old_tail: u64,
        pub new_tail: u64,
    }

    impl PmCopy for AppendListNodeEntry {}

    // This log entry represents an operation that writes a new list element
    // to the specified index in the specified ULL node. Note that the index
    // refers to the index in the list node's array, NOT the logical list
    // index that this operation updates.
    //
    // This type of log entry must contain the new list element to write, as
    // the insertion may update a live list element, which is a commiting update.
    // To avoid extra in-memory copying of the list element, we do not include
    // it directly in this structure.
    //
    // When this log entry is replayed:
    // 1) the list element immediately following it in the log is copied to
    //    the specified index in the specified list node.
    //
    // Note that this log entry type does not need to be used for appends.
    // Appending a new list element is a tentative update, as it is modifying
    // a list element outside the current bounds of the list, so it doesn't have
    // to be logged. This entry type only needs to be used for in-place updates
    // of in-bounds indices.
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct InsertListElementEntry {
        pub entry_type: u64,
        pub node_offset: u64,
        pub index_in_node: u64,
    }

    impl PmCopy for InsertListElementEntry {}

    // represents commit and invalidate metadata entries.
    // update entries record a CRC and use a different log entry type
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct MetadataLogEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
    }

    impl PmCopy for MetadataLogEntry {}

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct UpdateMetadataEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub new_crc: u64,
    }

    impl PmCopy for UpdateMetadataEntry {}
}
