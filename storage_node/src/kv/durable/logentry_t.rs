//! This file contains the definitions and `Serializable`
//! implementations for various log entry types for the
//! durable store. These are trusted because their structure,
//! and `Serializable` implementations, need to be manually
//! audited to ensure they accurately reflect their
//! byte-level Rust representations.
//!

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This log entry can either represent an item commit operation, when a
    // new key is added or an existing item is updated, or an item invalidation
    // operation, when a key is deleted or an existing item is updated.
    // Both entry types only require a table index to be logged.
    //
    // If this entry is used to log an item commit operation, the item being
    // added at this index should already have been written and made durable.
    // We do not log the CRC with the item commit operation because the CRC written
    // to the entry in should have been calculated as if the valid bit was already set.
    // This saves us some space in the log and updates when replaying the log.
    // It doesn't matter that the CRC is not technically correct for the entry
    // until the valid bit is set because the entry will not be visible until
    // the bit is set, which makes the CRC valid.
    //
    // If this entry is used to log an item invalidation operation, no further updates
    // are required to deallocate the item. The old contents will be overwritten when
    // the slot is used again.
    //
    // When this log entry is replayed, the item at the specified index should have its
    // valid bit set/cleared (depending on the entry type.)
    #[repr(C)]
    pub struct ItemTableEntry {
        entry_type: u64
        table_index: u64,
    }

    // This log entry represents an operation that appends a new list node
    // (i.e., an array of list elements, plus a next pointer and CRC) to
    // the list associated with the index at `list_metadata_index`.
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
    pub struct AppendListNodeEntry {
        entry_type: u64,
        list_metadata_index: u64,
        old_tail: u64,
        new_tail: u64,
    }

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
    pub struct InsertListElementEntry {
        entry_type: u64,
        node_offset: u64,
        index_in_node: u64,
        // list_element: L
    }

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
    pub struct UpdateListLenEntry {
        entry_type: u64,
        list_metadata_index: u64,
        new_length: u64,
    }

    // This log entry represents a list trim operation. It includes the
    // values with which to update the corresponding list metadata structure,
    // not the arguments passed in by the user.
    // When this log entry is replayed:
    // 1) The list metadata structure at the specified index has its head,
    //    length, and start index fields updated with those in the log entry,
    //    as well as a corresponding CRC update.
    #[repr(C)]
    pub struct TrimListEntry {
        entry_type: u64,
        list_metadata_index: u64,
        new_head_node: u64,
        new_list_len: u64,
        new_list_start_index: u64,
    }
}
