//! This file contains the definitions and `Serializable`
//! implementations for various log entry types for the
//! durable store. These are trusted because their structure,
//! and `Serializable` implementations, need to be manually
//! audited to ensure they accurately reflect their
//! byte-level Rust representations.
//!
//! TODO: the organization of this file and of logentry_v doesn't make much sense;
//! move things so that they are in the correct _t or _v file.

use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

use crate::kv::durable::logentry_v::*;
use crate::pmem::serialization_t::*;

verus! {

    // TODO: take out the padding, just read the type first and then deserialize 
    // the whole thing

    // NOTE ABOUT PADDING: some log entries have a relatively large amount of
    // padding (i.e., unused bytes that are included as fields in the struct).
    // This ensures that we can always check CRCs *before* checking each log
    // entry's type. If log entries were not of uniform size, we would have
    // to read the log entry type to determine its size prior to doing CRC
    // checks. However, since we haven't checked the CRC yet, the entry type
    // could have been corrupted, and we can't prove that we are reading
    // the entry type that we think we are. Note that when inserting list
    // entries, the log entry and the logged list element have separate CRCs
    // so that we can read and check them separately.

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
    pub struct CommitItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
        pub metadata_index: u64,
        pub metadata_crc: u64,
        pub _padding1: u128,
    }

    impl Serializable for CommitItemEntry {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.item_index) +
            spec_u64_to_le_bytes(self.metadata_index) + 
            spec_u64_to_le_bytes(self.metadata_crc) +
            spec_u128_to_le_bytes(self._padding1)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                )),
                item_index: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ENTRY + 8
                )),
                metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ENTRY + 8
                )),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_CRC_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_CRC_COMMIT_ENTRY + 8
                )),
                _padding1: spec_u128_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_PADDING_1_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_PADDING_1_COMMIT_ENTRY + 16
                )),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_item_index = #[trigger] spec_u64_to_le_bytes(s.item_index);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_padding1 = #[trigger] spec_u128_to_le_bytes(s._padding1);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ENTRY + 8
                    ) == serialized_item_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ENTRY + 8
                    ) == serialized_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_CRC_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_CRC_COMMIT_ENTRY + 8
                    ) == serialized_crc
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_1_COMMIT_ENTRY as int,
                        RELATIVE_POS_OF_PADDING_1_COMMIT_ENTRY + 16
                    ) == serialized_padding1
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
    }

    #[repr(C)]
    pub struct InvalidateItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
        pub _padding0: u128,
        pub _padding1: u128,
    }

    impl Serializable for InvalidateItemEntry {
        open spec fn spec_serialize(self) -> Seq<u8> 
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.item_index) +
            spec_u128_to_le_bytes(self._padding0) +
            spec_u128_to_le_bytes(self._padding1)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                item_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ENTRY as int, RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ENTRY + 8)),
                _padding0: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_0_INVALIDATE_ENTRY as int, RELATIVE_POS_OF_PADDING_0_INVALIDATE_ENTRY + 16)),
                _padding1: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_1_INVALIDATE_ENTRY as int, RELATIVE_POS_OF_PADDING_1_INVALIDATE_ENTRY + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_item_index = #[trigger] spec_u64_to_le_bytes(s.item_index);
                let serialized_padding0 = #[trigger] spec_u128_to_le_bytes(s._padding0);
                let serialized_padding1 = #[trigger] spec_u128_to_le_bytes(s._padding1);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ENTRY as int,
                        RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ENTRY + 8
                    ) == serialized_item_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_0_INVALIDATE_ENTRY as int,
                        RELATIVE_POS_OF_PADDING_0_INVALIDATE_ENTRY + 16
                    ) == serialized_padding0
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_1_INVALIDATE_ENTRY as int,
                        RELATIVE_POS_OF_PADDING_1_INVALIDATE_ENTRY + 16
                    ) == serialized_padding1
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
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
        pub entry_type: u64,
        pub list_metadata_index: u64,
        pub old_tail: u64,
        pub new_tail: u64,
        pub metadata_crc: u64,
        pub _padding0: u64,
    }

    impl Serializable for AppendListNodeEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.list_metadata_index) +
            spec_u64_to_le_bytes(self.old_tail) +
            spec_u64_to_le_bytes(self.new_tail) +
            spec_u64_to_le_bytes(self.metadata_crc) +
            spec_u64_to_le_bytes(self._padding0)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                list_metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE + 8)),
                old_tail: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE as int, RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE + 8)),
                new_tail: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE as int, RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE + 8)),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE as int, RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE + 8)),
                _padding0: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_0_APPEND_NODE as int, RELATIVE_POS_OF_PADDING_0_APPEND_NODE + 8))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_list_metadata_index = #[trigger] spec_u64_to_le_bytes(s.list_metadata_index);
                let serialized_old_tail = #[trigger] spec_u64_to_le_bytes(s.old_tail);
                let serialized_new_tail = #[trigger] spec_u64_to_le_bytes(s.new_tail);
                let serialized_metadata_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_padding = #[trigger] spec_u64_to_le_bytes(s._padding0);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE as int,
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE + 8
                    ) == serialized_list_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE as int,
                        RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE + 8
                    ) == serialized_old_tail
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE as int,
                        RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE + 8
                    ) == serialized_new_tail
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE as int,
                        RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE + 8
                    ) == serialized_metadata_crc
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_0_APPEND_NODE as int,
                        RELATIVE_POS_OF_PADDING_0_APPEND_NODE + 8
                    ) == serialized_padding
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
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
        pub entry_type: u64,
        pub node_offset: u64,
        pub index_in_node: u64,
        pub _padding0: u64,
        pub _padding1: u128,
    }

    impl Serializable for InsertListElementEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.node_offset) +
            spec_u64_to_le_bytes(self.index_in_node) +
            spec_u64_to_le_bytes(self._padding0) +
            spec_u128_to_le_bytes(self._padding1)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                node_offset: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT as int, RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT + 8)),
                index_in_node: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT as int, RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT + 8)),
                _padding0: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_0_INSERT_LIST_ELEMENT as int, RELATIVE_POS_OF_PADDING_0_INSERT_LIST_ELEMENT + 8)),
                _padding1: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_1_INSERT_LIST_ELEMENT as int, RELATIVE_POS_OF_PADDING_1_INSERT_LIST_ELEMENT + 16))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_node_offset = #[trigger] spec_u64_to_le_bytes(s.node_offset);
                let serialized_index_in_node = #[trigger] spec_u64_to_le_bytes(s.index_in_node);
                let serialized_padding0 = #[trigger] spec_u64_to_le_bytes(s._padding0);
                let serialized_padding1 = #[trigger] spec_u128_to_le_bytes(s._padding1);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT as int,
                        RELATIVE_POS_OF_NODE_OFFSET_INSERT_LIST_ELEMENT + 8
                    ) == serialized_node_offset
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT as int,
                        RELATIVE_POS_OF_INDEX_IN_NODE_INSERT_LIST_ELEMENT + 8
                    ) == serialized_index_in_node
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_0_INSERT_LIST_ELEMENT as int,
                        RELATIVE_POS_OF_PADDING_0_INSERT_LIST_ELEMENT + 8
                    ) == serialized_padding0
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_1_INSERT_LIST_ELEMENT as int,
                        RELATIVE_POS_OF_PADDING_1_INSERT_LIST_ELEMENT + 16
                    ) == serialized_padding1
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
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
        pub entry_type: u64,
        pub list_metadata_index: u64,
        pub new_length: u64,
        pub metadata_crc: u64,
        pub _padding0: u128,
    }

    impl Serializable for UpdateListLenEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.list_metadata_index) +
            spec_u64_to_le_bytes(self.new_length) +
            spec_u64_to_le_bytes(self.metadata_crc) +
            spec_u128_to_le_bytes(self._padding0)
            
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                list_metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN + 8)),
                new_length: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN + 8)),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN + 8)),
                _padding0: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_PADDING_0_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_PADDING_0_UPDATE_LIST_LEN + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_list_metadata_index = #[trigger] spec_u64_to_le_bytes(s.list_metadata_index);
                let serialized_new_len = #[trigger] spec_u64_to_le_bytes(s.new_length);
                let serialized_metadata_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_padding0 = #[trigger] spec_u128_to_le_bytes(s._padding0);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN + 8
                    ) == serialized_list_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN + 8
                    ) == serialized_new_len
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN + 8
                    ) == serialized_metadata_crc
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_PADDING_0_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_PADDING_0_UPDATE_LIST_LEN + 16
                    ) == serialized_padding0
                
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
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
        pub entry_type: u64,
        pub list_metadata_index: u64,
        pub new_head_node: u64,
        pub new_list_len: u64,
        pub new_list_start_index: u64,
        pub metadata_crc: u64, 
    }

    impl Serializable for TrimListEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.list_metadata_index) +
            spec_u64_to_le_bytes(self.new_head_node) +
            spec_u64_to_le_bytes(self.new_list_len) +
            spec_u64_to_le_bytes(self.new_list_start_index) +
            spec_u64_to_le_bytes(self.metadata_crc)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                list_metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST + 8)),
                new_head_node: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST as int, RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST + 8)),
                new_list_len: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST as int, RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST + 8)),
                new_list_start_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST as int, RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST + 8)),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST as int, RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST + 8))
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_list_metadata_index = #[trigger] spec_u64_to_le_bytes(s.list_metadata_index);
                let serialized_new_head_node = #[trigger] spec_u64_to_le_bytes(s.new_head_node);
                let serialized_new_list_len = #[trigger] spec_u64_to_le_bytes(s.new_list_len);
                let serialized_new_list_start_index = #[trigger] spec_u64_to_le_bytes(s.new_list_start_index);
                let serialized_metadata_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST as int,
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_TRIM_LIST + 8
                    ) == serialized_list_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST as int,
                        RELATIVE_POS_OF_NEW_HEAD_NODE_TRIM_LIST + 8
                    ) == serialized_new_head_node
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST as int,
                        RELATIVE_POS_OF_NEW_LIST_LEN_TRIM_LIST + 8
                    ) == serialized_new_list_len
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST as int,
                        RELATIVE_POS_OF_NEW_LIST_START_INDEX_TRIM_LIST + 8
                    ) == serialized_new_list_start_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST as int,
                        RELATIVE_POS_OF_METADATA_CRC_TRIM_LIST + 8
                    ) == serialized_metadata_crc
            });
        }

        proof fn lemma_auto_deserialize_serialize()
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_LOG_ENTRY
        }
    }

    pub struct CommitMetadataEntry 
    {
        pub entry_type: u64,
        pub list_metadata_index: u64,
        pub _padding0: u128,
        pub _padding1: u128,
    }

    impl Serializable for CommitMetadataEntry 
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) + 
            spec_u64_to_le_bytes(self.list_metadata_index) + 
            spec_u128_to_le_bytes(self._padding0) +
            spec_u128_to_le_bytes(self._padding1) 
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                list_metadata_index: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_CREATE_LIST as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_CREATE_LIST + 8)),
                _padding0: spec_u128_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_PADDING_0_CREATE_LIST as int, RELATIVE_POS_OF_PADDING_0_CREATE_LIST + 16)),
                _padding1: spec_u128_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_PADDING_1_CREATE_LIST as int, RELATIVE_POS_OF_PADDING_1_CREATE_LIST + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_list_metadata_index = #[trigger] spec_u64_to_le_bytes(s.list_metadata_index);
                let serialized_padding0 = #[trigger] spec_u128_to_le_bytes(s._padding0);
                let serialized_padding1 = #[trigger] spec_u128_to_le_bytes(s._padding1);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                ) == serialized_entry_type 
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_CREATE_LIST as int,
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_CREATE_LIST + 8
                ) == serialized_list_metadata_index
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_PADDING_0_CREATE_LIST as int,
                    RELATIVE_POS_OF_PADDING_0_CREATE_LIST + 16
                ) == serialized_padding0
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_PADDING_1_CREATE_LIST as int,
                    RELATIVE_POS_OF_PADDING_1_CREATE_LIST + 16
                ) == serialized_padding1
            });
        }

        proof fn lemma_auto_deserialize_serialize() 
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64 
        {
            LENGTH_OF_LOG_ENTRY
        }
    }


    pub struct InvalidateMetadataEntry
    {
        pub entry_type: u64,
        pub list_metadata_index: u64,
        pub _padding0: u128,
        pub _padding1: u128,
    }

    impl Serializable for InvalidateMetadataEntry 
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) + 
            spec_u64_to_le_bytes(self.list_metadata_index) +
            spec_u128_to_le_bytes(self._padding0) +
            spec_u128_to_le_bytes(self._padding1) 
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                list_metadata_index: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_DELETE_LIST as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_DELETE_LIST + 8)),
                _padding0: spec_u128_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_PADDING_0_DELETE_LIST as int, RELATIVE_POS_OF_PADDING_0_DELETE_LIST + 16)),
                _padding1: spec_u128_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_PADDING_1_DELETE_LIST as int, RELATIVE_POS_OF_PADDING_1_DELETE_LIST + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_list_metadata_index = #[trigger] spec_u64_to_le_bytes(s.list_metadata_index);
                let serialized_padding0 = #[trigger] spec_u128_to_le_bytes(s._padding0);
                let serialized_padding1 = #[trigger] spec_u128_to_le_bytes(s._padding1);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                ) == serialized_entry_type 
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_DELETE_LIST as int,
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_DELETE_LIST + 8
                ) == serialized_list_metadata_index
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_PADDING_0_DELETE_LIST as int,
                    RELATIVE_POS_OF_PADDING_0_DELETE_LIST + 16
                ) == serialized_padding0 
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_PADDING_1_DELETE_LIST as int,
                    RELATIVE_POS_OF_PADDING_1_DELETE_LIST + 16
                ) == serialized_padding1
            });
        }

        proof fn lemma_auto_deserialize_serialize() 
        {
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
            LENGTH_OF_LOG_ENTRY as int
        }

        fn serialized_len() -> u64 
        {
            LENGTH_OF_LOG_ENTRY   
        }
    }
}
