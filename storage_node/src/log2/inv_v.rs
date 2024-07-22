use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::subregion_v::*;
use crate::log2::layout_v::*;
use crate::log2::logimpl_v::*;
use crate::log2::logspec_t::*;

verus! {
pub open spec fn metadata_types_set(mem: Seq<u8>, log_start_addr: u64) -> bool 
{
    let cdb = u64::spec_from_bytes(extract_bytes(mem, log_start_addr as nat, u64::spec_size_of()));
    let metadata_pos = if cdb == CDB_TRUE { log_start_addr + spec_log_header_pos_cdb_true() }
                        else { log_start_addr + spec_log_header_pos_cdb_false() };
    let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
    let crc_pos =  metadata_pos + LogMetadata::spec_size_of();
    let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
    &&& u64::bytes_parseable(extract_bytes(mem, log_start_addr as nat, u64::spec_size_of()))
    &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
    &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
    &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
    &&& crc == spec_crc_u64(metadata.spec_to_bytes())
}

// This invariant says that there are no outstanding writes to the
// activate metadata subregion of the persistent-memory region
// (i.e., everything but the log area and the log metadata
// corresponding to `!cdb`). It also says that that metadata is
// consistent with the log information in `info` and various other
// in-memory variables given in parameters. The parameters to this
// function are:
//
// `pm_region_view` -- the current view of the persistent memory region
//
// `log_id` -- the GUID of the log
//
// `cdb` -- the current boolean value of the corruption-detection
// boolean
//
// `info` -- various variables describing information about this
// log
pub open spec fn metadata_consistent_with_info(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: u64,
    log_size: u64,
    cdb: bool,
    info: LogInfo,
) -> bool
{
    let mem = pm_region_view.committed();
    let log_metadata = deserialize_log_metadata(mem, log_start_addr, cdb);
    let log_crc = spec_get_active_log_crc(mem, log_start_addr, cdb);

    // No outstanding writes to global metadata, region metadata, or the log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range(log_start_addr as int, log_start_addr + u64::spec_size_of())
    // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range(log_start_addr + spec_get_active_log_metadata_pos(cdb),
            log_start_addr + spec_get_active_log_crc_end(cdb))

    // All the CRCs match
    &&& log_crc == log_metadata.spec_crc()

    // Various fields are valid and match the parameters to this function
    &&& log_metadata.head == info.head
    &&& log_metadata.log_length == info.log_length

    // The memory region is large enough to hold the entirety of the log area
    &&& mem.len() >= spec_log_area_pos() + info.log_area_len
}

pub open spec fn info_consistent_with_log_area_in_region(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: u64,
    log_size: u64,
    info: LogInfo,
    state: AbstractLogState,
) -> bool
{
    &&& pm_region_view.len() >= log_start_addr + spec_log_header_area_size() + info.log_area_len
    &&& info_consistent_with_log_area(
           get_subregion_view(pm_region_view, log_start_addr + spec_log_header_area_size(), info.log_area_len as nat),
           info,
           state
       )
}

// This invariant says that the log area of the given
// persistent-memory region view is consistent with both the log
// information `info` and the abstract log state `state`. Also,
// `info` satisfies certain invariant properties and is consistent
// with `state`.
//
// This means three things for every relative log position
// `pos` and its corresponding persistent-memory byte `pmb`:
//
// 1) If `0 <= pos < log_length`, then `pmb` has no outstanding
// writes and its committed content is the byte in the abstract
// log at position `pos`. This is critical so that recovery will
// recover to the right abstract log.
//
// 2) If `log_length <= pos < log_plus_pending_length`, then `pmb`
// may or may not have outstanding writes. But when/if it gets
// flushed, its content will be the byte in the abstract pending
// appends at position `pos - log_length`. This is useful so that,
// when a commit is requested, a flush is all that's needed to
// durably write the pending appends.
//
// 3) If `log_plus_pending_length <= pos < log_area_len`, then
// `pmb` has no outstanding writes because it's past the pending
// tail. This is useful so that, if there are further pending
// appends, they can be written into this part of the log area.
pub open spec fn info_consistent_with_log_area(
    log_area_view: PersistentMemoryRegionView,
    info: LogInfo,
    state: AbstractLogState,
) -> bool
{
    // `info` satisfies certain invariant properties
    &&& info.log_area_len >= MIN_LOG_AREA_SIZE
    &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
    &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
    &&& info.head + info.log_plus_pending_length <= u128::MAX

    // `info` and `state` are consistent with each other
    &&& state.log.len() == info.log_length
    &&& state.pending.len() == info.log_plus_pending_length - info.log_length
    &&& state.head == info.head
    &&& state.capacity == info.log_area_len

    // The log area is consistent with `info` and `state`
    &&& forall |pos_relative_to_head: int| {
            let log_area_offset =
                #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                info.head_log_area_offset as int,
                                                                info.log_area_len as int);
            let pmb = log_area_view.state[log_area_offset];
            &&& 0 <= pos_relative_to_head < info.log_length ==> {
                    &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
                    &&& pmb.outstanding_write.is_none()
                }
            &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                    pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
            &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len ==>
                    pmb.outstanding_write.is_none()
        }
}

}