#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::logentry_t::*;
use crate::multilog::multilogspec_t::*;
use crate::pmem::serialization_t::*;

verus! {

    // Enum representing different op log entry types.
    // We don't use an enum in the implementation so that we can have
    // control over size/layout of entries, but since this will only be
    // used in ghost code, an enum is fine.
    pub enum OpLogEntryType {
        ItemTableEntryCommit { table_index: u64 },
        ItemTableEntryInvalidate { table_index: u64 },
        AppendListNode {
            list_metadata_index: u64,
            old_tail: u64,
            new_tail: u64
        },
        InsertListElement {
            node_offset: u64,
            index_in_node: u64,
            // list_element: L
        },
        UpdateListLen {
            list_metadata_index: u64,
            new_length: u64,
        },
        TrimList {
            list_metadata_index: u64,
            new_head_node: u64,
            new_list_len: u64,
            new_list_start_index: u64,
        },
        CreateListTableEntry {
            list_metadata_index: u64,
            head: u64,
            // this will also include a key, but we write that separately
        },
        DeleteListTableEntry {
            list_metadata_index: u64,
        }
    }

    // Abstract state of the log as it is used in the KV store.
    // There is a small set of legal log entry types, and the only
    // way to free up space is to completely clear the log by moving
    // the head pointer to the tail. Once the log has been committed
    // it is illegal to perform any additional appends until it has
    // been cleared.
    pub struct AbstractOpLogState<K, L>
        where
            K: Serializable,
            L: Serializable
    {
        pub log_state: AbstractLogState,
        pub op_list: Seq<OpLogEntryType>,
        // stored separately from op_list so that item list;s recovery fn can ignore L
        pub list_entry_map: Map<OpLogEntryType, L>,
        pub op_list_committed: bool,
        pub _phantom: Option<K>,
    }

    impl<K, L> AbstractOpLogState<K, L>
        where
            K: Serializable,
            L: Serializable
    {
        pub open spec fn initialize(capacity: int) -> Self {
            Self {
                log_state: AbstractLogState::initialize(capacity),
                op_list: Seq::empty(),
                list_entry_map: Map::empty(),
                op_list_committed: false,
                _phantom: None
            }
        }

        // Note: this function covers both types of item table entry (commit and
        // invalidate) because they share a concrete op log entry type. This
        // is a bit funky because these types are represented in ghost code
        // by separate enum variants, but this makes the spec fn cleaner.
        pub open spec fn tentatively_append_item_table_entry(
            self,
            entry: &ItemTableEntry
        ) -> Self
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::ItemTableEntryCommit { table_index: entry.table_index }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_append_append_list_node_entry(
            self,
            entry: &AppendListNodeEntry
        ) -> Self
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::AppendListNode {
                    list_metadata_index: entry.list_metadata_index,
                    old_tail: entry.old_tail,
                    new_tail: entry.new_tail
                }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_append_insert_list_element_entry(
            self,
            entry: &InsertListElementEntry,
            list_element: &L
        ) -> Self
        {
            let op_log_entry = OpLogEntryType::InsertListElement {
                node_offset: entry.node_offset,
                index_in_node: entry.index_in_node,
            };
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize() + list_element.spec_serialize()),
                op_list: self.op_list.push(op_log_entry),
                list_entry_map: self.list_entry_map.insert(op_log_entry, *list_element),
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_append_update_list_len_entry(
            self,
            entry: &UpdateListLenEntry
        ) -> Self
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::UpdateListLen {
                    list_metadata_index: entry.list_metadata_index,
                    new_length: entry.new_length,
                }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_append_trim_list_entry(
            self,
            entry: &TrimListEntry
        ) -> Self
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::TrimList {
                    list_metadata_index: entry.list_metadata_index,
                    new_head_node: entry.new_head_node,
                    new_list_len: entry.new_list_len,
                    new_list_start_index: entry.new_list_start_index,
                }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_append_create_list_entry(
            self,
            entry: &CreateListEntry,
            key: &K,
        ) -> Self 
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize() + key.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::CreateListTableEntry { list_metadata_index: entry.list_metadata_index, head: entry.head }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn tentatively_delete_list_entry(
            self,
            entry: &DeleteListEntry
        ) -> Self 
        {
            Self {
                log_state: self.log_state.tentatively_append(entry.spec_serialize()),
                op_list: self.op_list.push(OpLogEntryType::DeleteListTableEntry { list_metadata_index: entry.list_metadata_index }),
                list_entry_map: self.list_entry_map,
                op_list_committed: false,
                _phantom: None
            }
        }

        pub open spec fn commit_op_log(self) -> Self
        {
            Self {
                log_state: self.log_state.commit(),
                op_list: self.op_list,
                list_entry_map: self.list_entry_map,
                op_list_committed: true,
                _phantom: None
            }
        }

        // TODO: use a more informative error code?
        pub open spec fn clear_log(self) -> Result<Self, ()>
        {
            if self.op_list_committed {
                Err(())
            } else {
                Ok(Self {
                    // abstract log state doesn't store the tail directly, so we have to calculate it here
                    log_state: self.log_state.advance_head(self.log_state.head + self.log_state.log.len()),
                    op_list: Seq::empty(),
                    list_entry_map: Map::empty(),
                    op_list_committed: false,
                    _phantom: None
                })
            }
        }
    }
}
