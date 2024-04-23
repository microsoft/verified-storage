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
    // We don't use an enum for these values so that we can represent
    // them in only 1 byte (enum variants are larger)

    pub const ALLOCATE_ITEM_TABLE_ENTRY: u8 = 0;
    pub const COMMIT_ITEM_TABLE_ENTRY: u8 = 1;
    pub const INVALIDATE_ITEM_TABLE_ENTRY: u8 = 2; // also implies deallocation

    // pub const VALIDATE_ITEM_ENTRY: u8 = 0; // TODO: this is unclear
    // pub const INVALIDATE_ITEM_ENTRY: u8 = 1;
    // pub const DELETE_ITEM_ENTRY: u8 = 2; // TODO: you don't need this -- invalid items are free
    // pub const UPDATE_LIST_ENTRY: u8 = 3;
    // pub const APPEND_TO_EXISTING_NODE_ENTRY: u8 = 4;
    // pub const APPEND_NODE_ENTRY: u8 = 5;
    // pub const SET_NEW_HEAD_ENTRY: u8 = 6;
    // pub const DELETE_NODES_ENTRY: u8 = 7; // TODO: you don't need this either -- unreachable nodes are free
    // // TODO: log entries for allocating/deallocating resources? avoid the need for big scans at startup -- could use bitmaps to record allocation information

}
