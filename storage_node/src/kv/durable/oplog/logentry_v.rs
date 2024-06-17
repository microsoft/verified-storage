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

use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
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
    pub const UPDATE_LIST_LEN_ENTRY: u64 = 4; // for new (appended) or in-place element updates
    pub const TRIM_LIST_METADATA_UPDATE_ENTRY: u64 = 5; // updates head, len, and start index during trim
    pub const COMMIT_METADATA_ENTRY: u64 = 6;
    pub const INVALIDATE_METADATA_ENTRY: u64 = 7;

    // layout constants for concrete log entry types
    // the entry type is first in all entries
    pub const RELATIVE_POS_OF_LOG_ENTRY_TYPE: u64 = 0;


    // commit item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM: u64 = 8;
    pub const RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM: u64 = 16;
    pub const RELATIVE_POS_OF_CRC_COMMIT_ITEM: u64 = 24;
    pub const LENGTH_OF_COMMIT_ITEM_ENTRY: u64 = 32;

    // invalidate item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM: u64 = 8;
    pub const LENGTH_OF_INVALIDATE_ITEM_ENTRY: u64 = 16;

    // append list node entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE: u64 = 8;
    pub const RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE: u64 = 16;
    pub const RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE: u64 = 24;
    pub const RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE: u64 = 32;
    pub const LENGTH_OF_APPEND_NODE_ENTRY: u64 = 40;

    // insert list element entry
    pub const RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT: u64 = 8;
    pub const RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT: u64 = 16;
    pub const LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY: u64 = 24;

    // update list length entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN: u64 = 8;
    pub const RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN: u64 = 16;
    pub const RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN: u64 = 24;
    pub const LENGTH_OF_UPDATE_LIST_LEN_ENTRY: u64 = 32;

    // trim list entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST: u64 = 8;
    pub const RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST: u64 = 16;
    pub const RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST: u64 = 24;
    pub const RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST: u64 = 32;
    pub const RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST: u64 = 40;
    pub const LENGTH_OF_TRIM_LIST_ENTRY: u64 = 48;

    // commit metadata entry 
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA: u64 = 8;
    pub const RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA: u64 = 16;
    pub const LENGTH_OF_COMMIT_METADATA_ENTRY: u64 = 24;

    // delete metadata entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA: u64 = 8;
    pub const LENGTH_OF_INVALIDATE_METADATA_ENTRY: u64 = 16;

    // Enum representing different op log entry types.
    // The concrete types we write to the log are not enums so that we have more control 
    // over layout; this enum is used represent log entries in ghost code and in DRAM 
    // during log replay
    pub enum OpLogEntryType<L>
        where
            L: PmCopy
    {
        ItemTableEntryCommit { 
            item_index: u64,
            metadata_index: u64,
            metadata_crc: u64,
        },
        ItemTableEntryInvalidate { item_index: u64 },
        AppendListNode {
            metadata_index: u64,
            old_tail: u64,
            new_tail: u64,
            metadata_crc: u64,
        },
        InsertListElement {
            node_offset: u64,
            index_in_node: u64,
            list_element: L
        },
        UpdateListLen {
            metadata_index: u64,
            new_length: u64,
            metadata_crc: u64,
        },
        TrimList {
            metadata_index: u64,
            new_head_node: u64,
            new_list_len: u64,
            new_list_start_index: u64,
            metadata_crc: u64,
        },
        CommitMetadataEntry {
            metadata_index: u64,
            item_index: u64,
        },
        InvalidateMetadataEntry {
            metadata_index: u64,
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
                metadata_index: value.metadata_index,
                metadata_crc: value.metadata_crc,
            }
        }

        pub exec fn to_commit_entry(self) -> Option<CommitItemEntry> {
            match self {
                OpLogEntryType::ItemTableEntryCommit { item_index, metadata_index, metadata_crc } => 
                    Some(CommitItemEntry {
                        entry_type: COMMIT_ITEM_TABLE_ENTRY,
                        item_index,
                        metadata_index,
                        metadata_crc,
                    }),
                _ => None
            }
        }

        pub exec fn from_invalidate_entry(value: Box<InvalidateItemEntry>) -> Self {
            OpLogEntryType::ItemTableEntryInvalidate { item_index: value.item_index }
        }

        pub exec fn to_invalidate_entry(self) -> Option<InvalidateItemEntry> {
            match self {
                OpLogEntryType::ItemTableEntryInvalidate { item_index } => 
                    Some(InvalidateItemEntry {
                        entry_type: INVALIDATE_ITEM_TABLE_ENTRY,
                        item_index,
                    }),
                _ => None
            }
        }

        pub exec fn from_append_list_node_entry(value: Box<AppendListNodeEntry>) -> Self {
            OpLogEntryType::AppendListNode { 
                metadata_index: value.metadata_index, 
                old_tail: value.old_tail, 
                new_tail: value.new_tail, 
                metadata_crc: value.metadata_crc 
            }
        }

        pub exec fn to_append_list_node_entry(self) -> Option<AppendListNodeEntry> {
            match self {
                OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail, metadata_crc } => 
                    Some(AppendListNodeEntry {
                        entry_type: APPEND_LIST_NODE_ENTRY,
                        metadata_index, 
                        old_tail,
                        new_tail, 
                        metadata_crc 
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

        pub exec fn to_insert_list_element_entry(self) -> Option<InsertListElementEntry> {
            match self {
                OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => 
                    Some(InsertListElementEntry { 
                        entry_type: INSERT_LIST_ELEMENT_ENTRY, 
                        node_offset, 
                        index_in_node
                    }),
                _ => None
            }
        }

        pub exec fn from_update_list_len_entry(value: Box<UpdateListLenEntry>) -> Self {
            OpLogEntryType::UpdateListLen { 
                metadata_index: value.metadata_index, 
                new_length: value.new_length, 
                metadata_crc: value.metadata_crc 
            }
        }

        pub exec fn to_update_list_len_entry(self) -> Option<UpdateListLenEntry> {
            match self {
                OpLogEntryType::UpdateListLen { metadata_index, new_length, metadata_crc } => 
                    Some(UpdateListLenEntry { 
                        entry_type: UPDATE_LIST_LEN_ENTRY,
                        metadata_index, 
                        new_length, 
                        metadata_crc 
                    }),
                    _ => None
            }
        }

        pub exec fn from_trim_list_entry(value: Box<TrimListEntry>) -> Self {
            OpLogEntryType::TrimList { 
                metadata_index: value.metadata_index, 
                new_head_node: value.new_head_node, 
                new_list_len: value.new_list_len, 
                new_list_start_index: value.new_list_start_index, 
                metadata_crc: value.metadata_crc 
            }
        }

        pub exec fn to_trim_list_entry(self) -> Option<TrimListEntry> {
            match self {
                OpLogEntryType::TrimList { metadata_index, new_head_node, new_list_len, new_list_start_index, metadata_crc } => 
                    Some(TrimListEntry { 
                        entry_type: TRIM_LIST_METADATA_UPDATE_ENTRY,
                        metadata_index, 
                        new_head_node, 
                        new_list_len, 
                        new_list_start_index, 
                        metadata_crc 
                    }),
                    _ => None 
            }
        }

        pub exec fn from_commit_metadata_entry(value: Box<CommitMetadataEntry>) -> Self {
            OpLogEntryType::CommitMetadataEntry { 
                metadata_index: value.metadata_index, 
                item_index: value.item_index 
            }
        }

        pub exec fn to_commit_metadata_entry(self) -> Option<CommitMetadataEntry> {
            match self {
                OpLogEntryType::CommitMetadataEntry { metadata_index, item_index } => 
                    Some(CommitMetadataEntry { 
                        entry_type: COMMIT_METADATA_ENTRY, 
                        metadata_index, 
                        item_index 
                    }),
                _ => None,
            }
        }

        pub exec fn from_invalidate_metadata_entry(value: Box<InvalidateMetadataEntry>) -> Self {
            OpLogEntryType::InvalidateMetadataEntry { metadata_index: value.metadata_index }
        }

        pub exec fn to_invalidate_metadata_entry(self) -> Option<InvalidateMetadataEntry> {
            match self {
                OpLogEntryType::InvalidateMetadataEntry { metadata_index } => 
                    Some(InvalidateMetadataEntry { entry_type: INVALIDATE_METADATA_ENTRY, metadata_index }),
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
        pub metadata_index: u64,
        pub metadata_crc: u64,
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
        pub metadata_crc: u64,
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

    // This log entry represents an update to a list's length field
    // in its metadata structure. The log entry should contain the actual
    // new length (not a number to add or subtract from the existing length)
    // to ensure that log replay is idempotent.
    //
    // When this log entry is replayed:
    // 1) The list metadata structure at the specified index has its length
    //    field updated to `new_length` and its CRC updated accordingly.
    //
    // This log entry acts as the committing write for list append operations.
    // The new list element should be written tentatively to an out-of-bounds
    // slot; it will become visible when the list length update is applied.
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct UpdateListLenEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub new_length: u64,
        pub metadata_crc: u64
    }


    impl PmCopy for UpdateListLenEntry {}

    // This log entry represents a list trim operation. It includes the
    // values with which to update the corresponding list metadata structure,
    // not the arguments passed in by the user.
    // When this log entry is replayed:
    // 1) The list metadata structure at the specified index has its head,
    //    length, and start index fields updated with those in the log entry,
    //    as well as a corresponding CRC update.
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct TrimListEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub new_head_node: u64,
        pub new_list_len: u64,
        pub new_list_start_index: u64,
        pub metadata_crc: u64, 
    }

    impl PmCopy for TrimListEntry {}

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct CommitMetadataEntry 
    {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub item_index: u64, // committing a metadata entry implies committing its item
    }

    impl CommitMetadataEntry 
    {
        pub exec fn new(metadata_index: u64, item_index: u64) -> Self 
        {
            Self {
                entry_type: COMMIT_METADATA_ENTRY,
                metadata_index,
                item_index,
            }
        }
    }

    impl PmCopy for CommitMetadataEntry {}

    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone)]
    pub struct InvalidateMetadataEntry
    {
        pub entry_type: u64,
        pub metadata_index: u64,
    }

    impl PmCopy for InvalidateMetadataEntry {}
}
