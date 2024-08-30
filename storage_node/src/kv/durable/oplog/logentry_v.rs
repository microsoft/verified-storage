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
use crate::kv::layout_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};


verus! {
    // Each concrete log entry corresponds to a logical
    // log entry type representing a logical operation on one 
    // of the components. We use these types both to 
    // represent logical operations in DRAM during execution
    // so they can be applied during commit and to abstractly
    // represent the state of the physical log.
    // Note that there are only log entries for the main table
    // and list area because recovering the item table does
    // not use logged info (although it does rely on info from
    // a recovered main table)
    #[derive(Debug)]
    pub enum LogicalOpLogEntry<L>
        where 
            L: PmCopy 
    {
        // Main table operations

        CommitMainTableEntry {
            index: u64,
        },
        InvalidateMainTableEntry {
            index: u64,
        },
        UpdateMainTableEntry {
            index: u64, 
            new_crc: u64, // we log the new CRC so we don't have to log the key and recalculate the CRC
            new_metadata: ListEntryMetadata,
        },

        // List area operations
        // // don't actually need this one! just need to use the list len to determine what 
        // // nodes have a valid next ptr and which don't
        // SetListNodeNext {
        //     node_index: u64,
        //     new_next: u64,
        // },
        UpdateListElement {
            node_index: u64,
            index_in_node: u64,
            list_element: L,
        },

        // This variant is NOT written to storage; it's used only in DRAM
        // to record which list nodes to deallocate during commit. We don't 
        // have to log it because it only represents a volatile operation 
        // (adding the nodes back to the allocator free list)
        NodeDeallocInMemory {
            old_head: u64,
            new_head: u64,
        }
    }

    // DRAM-only representation of a physical log entry, for use during recovery/
    // log installation.
    pub struct PhysicalOpLogEntry 
    {
        pub absolute_addr: u64,
        pub len: u64,
        pub bytes: Vec<u8>,
    }

    impl PhysicalOpLogEntry
    {
        pub open spec fn view(self) -> AbstractPhysicalOpLogEntry {
            AbstractPhysicalOpLogEntry {
                absolute_addr: self.absolute_addr as nat,
                len: self.len as nat,
                bytes: self.bytes@,
            }
        }

        pub open spec fn inv(self, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> bool {
            self@.inv(version_metadata, overall_metadata)
        }

        pub open spec fn log_inv(log: Vec<PhysicalOpLogEntry>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> bool {
            forall |i: int| 0 <= i < log.len() ==> #[trigger] log[i].inv(version_metadata, overall_metadata)
        }

        pub proof fn lemma_abstract_log_inv_implies_concrete_log_inv(log: Vec<PhysicalOpLogEntry>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata)
            requires
                ({
                    let log_view = Seq::new(log@.len(), |i: int| log[i]@);
                    AbstractPhysicalOpLogEntry::log_inv(log_view, version_metadata, overall_metadata)
                })
            ensures 
                PhysicalOpLogEntry::log_inv(log, version_metadata, overall_metadata)
        {
            let log_view = Seq::new(log@.len(), |i: int| log[i]@);
            assert(forall |i: int| 0 <= i < log.len() ==> #[trigger] log_view[i] == #[trigger] log[i]@);
            assert(forall |i: int| 0 <= i < log.len() ==> (#[trigger] log_view[i]).inv(version_metadata, overall_metadata));
            assert forall |i: int| 0 <= i < log.len() implies (#[trigger] log[i]@).inv(version_metadata, overall_metadata) by {
                assert(log[i]@ =~= log_view[i]);
            }
            assert forall |i: int| 0 <= i < log.len() implies (#[trigger] log[i]).inv(version_metadata, overall_metadata) by {
                let op = log[i];
                assert(op.absolute_addr == op@.absolute_addr);
                assert(op.len == op@.len);
                assert(op.absolute_addr + op.len <= overall_metadata.region_size);
            }
        }
    }
}