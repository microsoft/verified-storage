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

    // Item table update log entry types
    pub const COMMIT_ITEM_TABLE_ENTRY: u64 = 0;
    pub const INVALIDATE_ITEM_TABLE_ENTRY: u64 = 1;

    // List update log entry types
    pub const APPEND_LIST_NODE_ENTRY: u64 = 2;
    pub const INSERT_LIST_ELEMENT_ENTRY: u64 = 3;
    pub const UPDATE_LIST_LEN_ENTRY: u64 = 4; // for new (appended) or in-place element updates
    pub const TRIM_LIST_METADATA_UPDATE_ENTRY: u64 = 5; // updates head, len, and start index during trim
    pub const CREATE_LIST_ENTRY: u64 = 6;
    pub const DELETE_LIST_ENTRY: u64 = 7;

    // layout constants for concrete log entry types
    // the entry type is first in all entries
    pub const RELATIVE_POS_OF_LOG_ENTRY_TYPE: u64 = 0;
    // all log entries are the same size
    pub const LENGTH_OF_LOG_ENTRY: u64 = 48;


    // commit item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ENTRY: u64 = 8;
    pub const RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ENTRY: u64 = 16;
    pub const RELATIVE_POS_OF_CRC_COMMIT_ENTRY: u64 = 24;
    pub const RELATIVE_POS_OF_PADDING_1_COMMIT_ENTRY: u64 = 32;

    // invalidate item table entry
    pub const RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ENTRY: u64 = 8;
    pub const RELATIVE_POS_OF_PADDING_0_INVALIDATE_ENTRY: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING_1_INVALIDATE_ENTRY: u64 = 32;

    // append list node entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE: u64 = 8;
    pub const RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE: u64 = 16;
    pub const RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE: u64 = 24;
    pub const RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE: u64 = 32;
    pub const RELATIVE_POS_OF_PADDING_0_APPEND_NODE: u64 = 40;

    // insert list element entry
    pub const RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT: u64 = 8;
    pub const RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING_0_INSERT_LIST_ELEMENT: u64 = 24;
    pub const RELATIVE_POS_OF_PADDING_1_INSERT_LIST_ELEMENT: u64 = 32;

    // update list length entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN: u64 = 8;
    pub const RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN: u64 = 16;
    pub const RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN: u64 = 24;
    pub const RELATIVE_POS_OF_PADDING_0_UPDATE_LIST_LEN: u64 = 32;

    // trim list entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST: u64 = 8;
    pub const RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST: u64 = 16;
    pub const RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST: u64 = 24;
    pub const RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST: u64 = 32;
    pub const RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST: u64 = 40;

    // create list entry 
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_CREATE_LIST: u64 = 8;
    pub const RELATIVE_POS_OF_HEAD_CREATE_LIST: u64 = 16;
    pub const RELATIVE_POS_OF_ITEM_INDEX_CREATE_LIST: u64 = 24;
    pub const RELATIVE_POS_OF_PADDING_0_CREATE_LIST: u64 = 32;

    // delete list entry
    pub const RELATIVE_POS_OF_LIST_METADATA_INDEX_DELETE_LIST: u64 = 8;
    pub const RELATIVE_POS_OF_PADDING_0_DELETE_LIST: u64 = 16;
    pub const RELATIVE_POS_OF_PADDING_1_DELETE_LIST: u64 = 32;
}
