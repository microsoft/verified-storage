use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::kv::layout_v::OverallMetadata;
use crate::lemma_establish_extract_bytes_equivalence;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::subregion_v::*;
use crate::log2::layout_v::*;
use crate::log2::logimpl_v::*;
use crate::log2::logspec_t::*;
use crate::pmem::pmcopy_t::*;

verus! {
pub open spec fn metadata_types_set(mem: Seq<u8>, log_start_addr: nat) -> bool 
{
    let cdb = u64::spec_from_bytes(extract_bytes(mem, log_start_addr, u64::spec_size_of()));
    let metadata_pos = if cdb == CDB_TRUE { log_start_addr + spec_log_header_pos_cdb_true() }
                        else { log_start_addr + spec_log_header_pos_cdb_false() };
    let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
    let crc_pos =  metadata_pos + LogMetadata::spec_size_of();
    let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
    &&& u64::bytes_parseable(extract_bytes(mem, log_start_addr, u64::spec_size_of()))
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
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
) -> bool
{
    let mem = pm_region_view.committed();
    let log_metadata = spec_get_active_log_metadata(mem, log_start_addr, cdb);
    let log_crc = spec_get_active_log_crc(mem, log_start_addr, cdb);

    // No outstanding writes to global metadata, region metadata, or the log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range(log_start_addr as int, (log_start_addr + u64::spec_size_of()) as int)
    // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
    &&& pm_region_view.no_outstanding_writes_in_range((log_start_addr + spec_get_active_log_metadata_pos(cdb)) as int,
            (log_start_addr + spec_get_active_log_crc_end(cdb)) as int)

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
    log_start_addr: nat,
    log_size: nat,
    info: LogInfo,
    state: AbstractLogState,
) -> bool
{
    &&& pm_region_view.len() >= log_start_addr + log_size
    &&& info_consistent_with_log_area(
           get_subregion_view(pm_region_view, log_start_addr + spec_log_area_pos(),
                              (log_size - spec_log_area_pos()) as nat),
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

// This lemma proves that, for any address in the log area of the
// given persistent memory view, it corresponds to a specific
// logical position in the abstract log relative to the head. That
// logical position `pos` satisfies `0 <= pos < log_area_len`.
//
// It's useful to call this lemma because it takes facts that
// trigger `pm_region_view.state[addr]` and turns them into facts
// that trigger `relative_log_pos_to_log_area_offset`. That's the
// trigger used in `info_consistent_with_log_area_in_region`.
pub proof fn lemma_addresses_in_log_area_correspond_to_relative_log_positions(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    info: LogInfo
)
    requires
        pm_region_view.len() >= log_start_addr + spec_log_area_pos() + info.log_area_len,
        info.head_log_area_offset < info.log_area_len,
        info.log_area_len > 0,
    ensures
        forall |addr: int| #![trigger pm_region_view.state[addr]]
            log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + info.log_area_len ==> {
                let log_area_offset = addr - (log_start_addr + spec_log_area_pos());
                let pos_relative_to_head =
                    if log_area_offset >= info.head_log_area_offset {
                        log_area_offset - info.head_log_area_offset
                    }
                    else {
                        log_area_offset - info.head_log_area_offset + info.log_area_len
                    };
                &&& 0 <= pos_relative_to_head < info.log_area_len
                &&& addr == log_start_addr + spec_log_area_pos() +
                            relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                info.head_log_area_offset as int,
                                                                info.log_area_len as int)
            }
{}

pub proof fn lemma_auto_subranges_of_same_bytes_equal(mem1: Seq<u8>, mem2: Seq<u8>)
    requires
        mem1 == mem2 
    ensures
        forall |addr: int, len: int| 0 <= addr < addr + len < mem1.len() ==> {
            #[trigger] extract_bytes(mem1, addr as nat, len as nat) == #[trigger] extract_bytes(mem2, addr as nat, len as nat)
        }
{}

pub proof fn lemma_subranges_of_same_bytes_equal(mem1: Seq<u8>, mem2: Seq<u8>, addr: nat, len: nat)
    requires
        mem1 == mem2 
    ensures
        extract_bytes(mem1, addr as nat, len as nat) == extract_bytes(mem2, addr as nat, len as nat)
{}

// This lemma proves that a subrange of a subrange is equal to just obtaining the final subrange using its 
// absolute start index. This is obvious and requires no body, but having a dedicated lemma helps
// Z3 establish the equality
// TODO: do this about subranges rather than extract_bytes -- should be equivalent and more useful
pub proof fn lemma_subrange_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
    requires 
        start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
    ensures 
        ({
            let start_offset = start2 - start1;
            extract_bytes(extract_bytes(mem, start1, len1), start_offset as nat, len2) =~= 
                extract_bytes(mem, start2, len2)
        })
{}

// This lemma proves that two sequences of bytes that may contain valid logs, and their log
// subregions are equal, then the sequences recover to the same log. This is obvious
// but the proof is non-trivial because we need to explicitly prove the equality of 
// each relevant subrange.
pub proof fn lemma_same_bytes_recover_to_same_state(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    overall_metadata: OverallMetadata,
)
    requires
        mem1.len() == overall_metadata.region_size,
        mem1.len() == mem2.len(),
        extract_bytes(mem1, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
            extract_bytes(mem2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
        0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size < overall_metadata.region_size,
        0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
    ensures
        UntrustedLogImpl::recover(mem1, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) ==
            UntrustedLogImpl::recover(mem2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
    {
        let log_start_addr = overall_metadata.log_area_addr as nat;
        let log_size = overall_metadata.log_area_size as nat;

        lemma_establish_extract_bytes_equivalence(mem1, mem2);

        // Proves that the CDBs are the same
        lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr, log_size, u64::spec_size_of());
        let cdb1 = spec_check_log_cdb(mem1, log_start_addr);
        if let Some(cdb1) = cdb1 {
            let metadata_pos = spec_get_active_log_metadata_pos(cdb1); 
            let crc_pos = metadata_pos + LogMetadata::spec_size_of();
            // Proves that metadata, CRC, and log area are the same
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + metadata_pos, log_size, LogMetadata::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + crc_pos, log_size, u64::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + spec_log_area_pos(), log_size, (log_size - spec_log_area_pos()) as nat);
        } else {
            // both are None
        }
    }
}
