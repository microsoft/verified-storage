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

    // Enum representing different op log entry types.
    // The concrete types we write to the log are not enums so that we have more control 
    // over layout; this enum is used represent log entries in ghost code and in DRAM 
    // during log replay
    pub enum OpLogEntryType<L>
        where
            L: Serializable
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

    // This trait indicates which types are valid log entry types so that we can have a few
    // generic op log append functions (rather than one per op type)
    pub trait LogEntry : Serializable {
        // TODO: remove this method once the issue with the `Serializable` `as_bytes` method is fixed.
        // Ideally we would not have to manually serialize/copy log entries before writing them to PM.
        exec fn serialize_bytes(&self) -> (out: Vec<u8>)
            ensures 
                out@ =~= self.spec_serialize();

        // exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        //     requires 
        //         bytes@.len() == Self::spec_serialized_len()
        //     ensures 
        //         out == Self::spec_deserialize(bytes@);
    }

    // TODO: documentation
    #[repr(C)]
    pub struct CommitItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
        pub metadata_index: u64,
        pub metadata_crc: u64,
    }

    impl LogEntry for CommitItemEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut item_index_bytes = u64_to_le_bytes(self.item_index);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            let mut metadata_crc_bytes = u64_to_le_bytes(self.metadata_crc);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut item_index_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes.append(&mut metadata_crc_bytes);
            bytes
        }
    }

    impl Serializable for CommitItemEntry {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.item_index) +
            spec_u64_to_le_bytes(self.metadata_index) + 
            spec_u64_to_le_bytes(self.metadata_crc)
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
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM + 8
                )),
                metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM + 8
                )),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(
                        RELATIVE_POS_OF_CRC_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_CRC_COMMIT_ITEM + 8
                )),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_item_index = #[trigger] spec_u64_to_le_bytes(s.item_index);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_ITEM_INDEX_COMMIT_ITEM + 8
                    ) == serialized_item_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_METADATA_INDEX_COMMIT_ITEM + 8
                    ) == serialized_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_CRC_COMMIT_ITEM as int,
                        RELATIVE_POS_OF_CRC_COMMIT_ITEM + 8
                    ) == serialized_crc
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
            LENGTH_OF_COMMIT_ITEM_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_COMMIT_ITEM_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }

    #[repr(C)]
    pub struct InvalidateItemEntry {
        pub entry_type: u64,
        pub item_index: u64,
    }

    impl LogEntry for InvalidateItemEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut item_index_bytes = u64_to_le_bytes(self.item_index);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut item_index_bytes);
            bytes
        }
    }

    impl Serializable for InvalidateItemEntry {
        open spec fn spec_serialize(self) -> Seq<u8> 
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.item_index)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                item_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM as int, RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_item_index = #[trigger] spec_u64_to_le_bytes(s.item_index);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM as int,
                        RELATIVE_POS_OF_ITEM_INDEX_INVALIDATE_ITEM + 8
                    ) == serialized_item_index
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
            LENGTH_OF_INVALIDATE_ITEM_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_INVALIDATE_ITEM_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }

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
    pub struct AppendListNodeEntry {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub old_tail: u64,
        pub new_tail: u64,
        pub metadata_crc: u64,
    }

    impl LogEntry for AppendListNodeEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            let mut old_tail_bytes = u64_to_le_bytes(self.old_tail);
            let mut new_tail_bytes = u64_to_le_bytes(self.new_tail);
            let mut metadata_crc_bytes = u64_to_le_bytes(self.metadata_crc);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes.append(&mut old_tail_bytes);
            bytes.append(&mut new_tail_bytes);
            bytes.append(&mut metadata_crc_bytes);
            bytes
        }
    }

    impl Serializable for AppendListNodeEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.metadata_index) +
            spec_u64_to_le_bytes(self.old_tail) +
            spec_u64_to_le_bytes(self.new_tail) +
            spec_u64_to_le_bytes(self.metadata_crc)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE + 8)),
                old_tail: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE as int, RELATIVE_POS_OF_OLD_TAIL_APPEND_NODE + 8)),
                new_tail: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE as int, RELATIVE_POS_OF_NEW_TAIL_APPEND_NODE + 8)),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE as int, RELATIVE_POS_OF_METADATA_CRC_APPEND_NODE + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_old_tail = #[trigger] spec_u64_to_le_bytes(s.old_tail);
                let serialized_new_tail = #[trigger] spec_u64_to_le_bytes(s.new_tail);
                let serialized_metadata_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE as int,
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_APPEND_NODE + 8
                    ) == serialized_metadata_index
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
            LENGTH_OF_APPEND_NODE_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_APPEND_NODE_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
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
    }

    impl LogEntry for InsertListElementEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut node_offset_bytes = u64_to_le_bytes(self.node_offset);
            let mut index_in_node_bytes = u64_to_le_bytes(self.index_in_node);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut node_offset_bytes);
            bytes.append(&mut index_in_node_bytes);
            bytes
        }
    }

    impl Serializable for InsertListElementEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.node_offset) +
            spec_u64_to_le_bytes(self.index_in_node)
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
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_node_offset = #[trigger] spec_u64_to_le_bytes(s.node_offset);
                let serialized_index_in_node = #[trigger] spec_u64_to_le_bytes(s.index_in_node);
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
        }

        open spec fn spec_serialized_len() -> int
        {
            LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_INSERT_LIST_ELEMENT_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
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
        pub metadata_index: u64,
        pub new_length: u64,
        pub metadata_crc: u64
    }

    impl LogEntry for UpdateListLenEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            let mut new_length_bytes = u64_to_le_bytes(self.new_length);
            let mut metadata_crc_bytes = u64_to_le_bytes(self.metadata_crc);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes.append(&mut new_length_bytes);
            bytes.append(&mut metadata_crc_bytes);
            bytes
        }
    }

    impl Serializable for UpdateListLenEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.metadata_index) +
            spec_u64_to_le_bytes(self.new_length) +
            spec_u64_to_le_bytes(self.metadata_crc) 
            
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                entry_type: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                metadata_index: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN + 8)),
                new_length: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN + 8)),
                metadata_crc: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN as int, RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_new_len = #[trigger] spec_u64_to_le_bytes(s.new_length);
                let serialized_metadata_crc = #[trigger] spec_u64_to_le_bytes(s.metadata_crc);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                        RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                    ) == serialized_entry_type
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_LIST_METADATA_INDEX_UPDATE_LIST_LEN + 8
                    ) == serialized_metadata_index
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_NEW_LENGTH_UPDATE_LIST_LEN + 8
                    ) == serialized_new_len
                &&& serialized_entry.subrange(
                        RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN as int,
                        RELATIVE_POS_OF_METADATA_CRC_UPDATE_LIST_LEN + 8
                    ) == serialized_metadata_crc
             
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
            LENGTH_OF_UPDATE_LIST_LEN_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_UPDATE_LIST_LEN_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
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
        pub metadata_index: u64,
        pub new_head_node: u64,
        pub new_list_len: u64,
        pub new_list_start_index: u64,
        pub metadata_crc: u64, 
    }

    impl LogEntry for TrimListEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            let mut new_head_node_bytes = u64_to_le_bytes(self.new_head_node);
            let mut new_list_len_bytes = u64_to_le_bytes(self.new_list_len);
            let mut new_list_start_index_bytes = u64_to_le_bytes(self.new_list_start_index);
            let mut metadata_crc_bytes = u64_to_le_bytes(self.metadata_crc);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes.append(&mut new_head_node_bytes);
            bytes.append(&mut new_list_len_bytes);
            bytes.append(&mut new_list_start_index_bytes);
            bytes.append(&mut metadata_crc_bytes);
            bytes
        }
    }

    impl Serializable for TrimListEntry
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) +
            spec_u64_to_le_bytes(self.metadata_index) +
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
                metadata_index: spec_u64_from_le_bytes(
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
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
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
                    ) == serialized_metadata_index
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
            LENGTH_OF_TRIM_LIST_ENTRY as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_TRIM_LIST_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }

    pub struct CommitMetadataEntry 
    {
        pub entry_type: u64,
        pub metadata_index: u64,
        pub item_index: u64, // committing a metadata entry implies committing its item
    }

    impl LogEntry for CommitMetadataEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            let mut item_index_bytes = u64_to_le_bytes(self.item_index);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes.append(&mut item_index_bytes);
            bytes
        }
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

    impl Serializable for CommitMetadataEntry 
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) + 
            spec_u64_to_le_bytes(self.metadata_index) + 
            spec_u64_to_le_bytes(self.item_index) 
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                metadata_index: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA + 8)),
                item_index: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA as int, RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_item_index = #[trigger] spec_u64_to_le_bytes(s.item_index);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                ) == serialized_entry_type 
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA as int,
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_COMMIT_METADATA + 8
                ) == serialized_metadata_index
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA as int,
                    RELATIVE_POS_OF_ITEM_INDEX_COMMIT_METADATA + 8
                ) == serialized_item_index
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
        }

        open spec fn spec_serialized_len() -> int 
        {
            LENGTH_OF_COMMIT_METADATA_ENTRY as int
        }

        fn serialized_len() -> u64 
        {
            LENGTH_OF_COMMIT_METADATA_ENTRY
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }
    pub struct InvalidateMetadataEntry
    {
        pub entry_type: u64,
        pub metadata_index: u64,
    }

    impl LogEntry for InvalidateMetadataEntry {
        exec fn serialize_bytes(&self) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(Self::serialized_len() as usize);
            let mut entry_type_bytes = u64_to_le_bytes(self.entry_type);
            let mut metadata_index_bytes = u64_to_le_bytes(self.metadata_index);
            bytes.append(&mut entry_type_bytes);
            bytes.append(&mut metadata_index_bytes);
            bytes
        }
    }

    impl Serializable for InvalidateMetadataEntry 
    {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.entry_type) + 
            spec_u64_to_le_bytes(self.metadata_index) 
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self 
        {
            Self {
                entry_type: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LOG_ENTRY_TYPE as int, RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8)),
                metadata_index: spec_u64_from_le_bytes(bytes.subrange(RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA as int, RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA + 8)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_entry_type = #[trigger] spec_u64_to_le_bytes(s.entry_type);
                let serialized_metadata_index = #[trigger] spec_u64_to_le_bytes(s.metadata_index);
                let serialized_entry = #[trigger] s.spec_serialize();
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE as int,
                    RELATIVE_POS_OF_LOG_ENTRY_TYPE + 8
                ) == serialized_entry_type 
                &&& serialized_entry.subrange(
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA as int,
                    RELATIVE_POS_OF_LIST_METADATA_INDEX_INVALIDATE_METADATA + 8
                ) == serialized_metadata_index
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
            LENGTH_OF_INVALIDATE_METADATA_ENTRY as int
        }

        fn serialized_len() -> u64 
        {
            LENGTH_OF_INVALIDATE_METADATA_ENTRY   
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }
}
