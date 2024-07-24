use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::pmem::pmcopy_t::*;

verus! {
    pub closed spec fn logical_and_physical_logs_correspond<L>(
        logical_log: Seq<LogicalOpLogEntry<L>>,
        physical_log: Seq<AbstractPhysicalOpLogEntry>
    ) -> bool 
        where 
            L: PmCopy
    {
        // TODO: an actual way to check correspondence
        true 
    }
}