#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::metadata::layout_v::ListEntryMetadata;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::layout_v::OverallMetadata;
use crate::multilog::multilogspec_t::*;
use crate::pmem::pmcopy_t::*;

verus! {

    #[verifier::ext_equal]
    pub struct AbstractPhysicalOpLogEntry {
        pub offset: nat, // offset of this log entry relative to the beginning of the log
        pub absolute_addr: nat,
        pub len: nat,
        pub bytes: Seq<u8>,
    }

    impl AbstractPhysicalOpLogEntry {
        pub open spec fn inv(self, overall_metadata: OverallMetadata) -> bool {
            &&& self.len > 0
            &&& 0 <= self.absolute_addr < self.absolute_addr + self.len <= overall_metadata.region_size
            &&& ({
                ||| self.absolute_addr + self.len <= overall_metadata.log_area_addr
                ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= self.absolute_addr
            })
            &&& self.len == self.bytes.len()
        }

        pub open spec fn log_inv(log: Seq<Self>, overall_metadata: OverallMetadata) -> bool {
            forall |i: int| 0 <= i < log.len() ==> (#[trigger] log[i]).inv(overall_metadata)
        }
    }

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
        pub logical_op_list: Seq<LogicalOpLogEntry<L>>,
        pub physical_op_list: Seq<AbstractPhysicalOpLogEntry>,
        pub op_list_committed: bool,
    }

    impl<L> AbstractOpLogState<L>
        where
            L: PmCopy
    {
        pub open spec fn initialize() -> Self {
            Self {
                logical_op_list: Seq::empty(),
                physical_op_list: Seq::empty(),
                op_list_committed: false,
            }
        }

        pub open spec fn tentatively_append_log_entry(
            self,
            logical_log_entry: LogicalOpLogEntry<L>,
            physical_log_entry: AbstractPhysicalOpLogEntry,
        ) -> Self {
            Self {
                logical_op_list: self.logical_op_list.push(logical_log_entry),
                physical_op_list: self.physical_op_list.push(physical_log_entry),
                op_list_committed: false
            }
        }

        pub open spec fn commit_op_log(self) -> Self
        {
            Self {
                logical_op_list: self.logical_op_list,
                physical_op_list: self.physical_op_list,
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
                    logical_op_list: Seq::empty(),
                    physical_op_list: Seq::empty(),
                    op_list_committed: false,
                })
            }
        }
    }
}
