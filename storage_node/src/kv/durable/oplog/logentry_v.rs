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

use crate::kv::durable::maintablelayout_v::ListEntryMetadata;
use crate::kv::layout_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::util_v::*;
use deps_hack::PmCopy;


verus! {
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

        pub open spec fn vec_view(vec: Vec<Self>) -> Seq<AbstractPhysicalOpLogEntry>
        {
            Seq::new(vec@.len(), |i: int| vec[i]@)
        }
    }
}
