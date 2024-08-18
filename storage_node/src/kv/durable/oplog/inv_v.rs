use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::log2::logspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;

verus! {

// pub closed spec fn logical_and_physical_logs_correspond<L>(
//     logical_log: Seq<LogicalOpLogEntry<L>>,
//     physical_log: Seq<AbstractPhysicalOpLogEntry>
// ) -> bool 
//     where 
//         L: PmCopy + std::fmt::Debug + Copy,
// ;

// // This function indicates whether the CRC is correctly set at the end of 
// // a non-empty op log. It takes the abstract log state of the base log
// // as that is sufficient to determine whether the CRC is set or not
// pub open spec fn types_set(base_log_state: AbstractLogState) -> bool 
//     recommends
//         base_log_state.log.len() >= u64::spec_size_of()
// {
//     if base_log_state.log.len() == 0 {
//         // if the log is empty, this is vacuously true
//         true
//     } else {
//         let log_contents_bytes = extract_bytes(base_log_state.log, 0, base_log_state.log.len());
//         let crc_bytes = extract_bytes(base_log_state.log, (base_log_state.log.len() - u64::spec_size_of()) as nat, u64::spec_size_of());
//         let crc = u64::spec_from_bytes(crc_bytes);
//         &&& u64::bytes_parseable(crc_bytes)
//         &&& crc == spec_crc_u64(log_contents_bytes)
//     }
// }
}