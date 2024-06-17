#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::oplog::logentry_v::*;
use crate::multilog::multilogspec_t::*;
use crate::pmem::pmcopy_t::*;

verus! {

    // Abstract state of the log as it is used in the KV store.
    // There is a small set of legal log entry types, and the only
    // way to free up space is to completely clear the log by moving
    // the head pointer to the tail. Once the log has been committed
    // it is illegal to perform any additional appends until it has
    // been cleared.
    pub struct AbstractOpLogState<L>
        where
            L: PmCopy
    {
        pub op_list: Seq<OpLogEntryType<L>>,
        pub op_list_committed: bool,
    }

    impl<L> AbstractOpLogState<L>
        where
            L: PmCopy
    {
        pub open spec fn initialize(capacity: int) -> Self {
            Self {
                op_list: Seq::empty(),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_commit_item_entry(
            self,
            entry: &CommitItemEntry
        ) -> Self
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::ItemTableEntryCommit { 
                    item_index: entry.item_index,
                    metadata_index: entry.metadata_index ,
                    metadata_crc: entry.metadata_crc
                }),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_invalidate_item_entry(
            self,
            entry: &InvalidateItemEntry,
        ) -> Self 
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::ItemTableEntryInvalidate { item_index: entry.item_index }),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_append_list_node_entry(
            self,
            entry: &AppendListNodeEntry
        ) -> Self
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::AppendListNode {
                    metadata_index: entry.metadata_index,
                    old_tail: entry.old_tail,
                    new_tail: entry.new_tail,
                    metadata_crc: entry.metadata_crc,
                }),
                op_list_committed: false,
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
                list_element: *list_element,
            };
            Self {
                op_list: self.op_list.push(op_log_entry),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_update_list_len_entry(
            self,
            entry: &UpdateListLenEntry
        ) -> Self
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::UpdateListLen {
                    metadata_index: entry.metadata_index,
                    new_length: entry.new_length,
                    metadata_crc: entry.metadata_crc,
                }),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_trim_list_entry(
            self,
            entry: &TrimListEntry
        ) -> Self
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::TrimList {
                    metadata_index: entry.metadata_index,
                    new_head_node: entry.new_head_node,
                    new_list_len: entry.new_list_len,
                    new_list_start_index: entry.new_list_start_index,
                    metadata_crc: entry.metadata_crc,
                }),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_create_list_entry(
            self,
            entry: &CommitMetadataEntry,
        ) -> Self 
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::CommitMetadataEntry { 
                    metadata_index: entry.metadata_index, 
                    item_index: entry.item_index,
                }),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_delete_list_entry(
            self,
            entry: &InvalidateMetadataEntry
        ) -> Self 
        {
            Self {
                op_list: self.op_list.push(OpLogEntryType::InvalidateMetadataEntry { metadata_index: entry.metadata_index }),
                op_list_committed: false,
            }
        }

        pub open spec fn commit_op_log(self) -> Self
        {
            Self {
                op_list: self.op_list,
                op_list_committed: true,
            }
        }

        // TODO: use a more informative error code?
        pub open spec fn clear_log(self) -> Result<Self, ()>
        {
            if self.op_list_committed {
                Err(())
            } else {
                Ok(Self {
                    op_list: Seq::empty(),
                    op_list_committed: false,
                })
            }
        }
    }
}
