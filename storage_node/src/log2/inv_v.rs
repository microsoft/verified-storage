use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::kv::layout_v::OverallMetadata;
use crate::lemma_establish_extract_bytes_equivalence;
use crate::pmem::{crc_t::*, pmemspec_t::*, pmemutil_v::*, subregion_v::*, wrpm_t::*};
use crate::log2::layout_v::*;
use crate::log2::logimpl_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::util_v::*;

verus! {

// This invariant says that there are no outstanding writes to any
// part of the metadata subregion of the persistent-memory region.
// It's temporarily violated in the middle of various operations,
// of course, but it's always restored before finishing an
// operation.
pub open spec fn no_outstanding_writes_to_metadata(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
) -> bool
{
    no_outstanding_writes_in_range(pm_region_view, log_start_addr as int, (log_start_addr + spec_log_area_pos()) as int)
}

// This invariant is similar to no_outstanding_writes_to_metadata, except that it allows outstanding writes
// to the inactive log metadata region.
pub open spec fn no_outstanding_writes_to_active_metadata(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    cdb: bool,
) -> bool 
{
    // Note that we include the active log metadata's CRC in the region
    let metadata_pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
    &&& no_outstanding_writes_in_range(pm_region_view,
        metadata_pos as int, (metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) as int)
    &&& no_outstanding_writes_in_range(pm_region_view, log_start_addr as int, (log_start_addr + u64::spec_size_of()) as int)
}

pub open spec fn active_metadata_is_equal(
    pm_region_view1: PersistentMemoryRegionView,
    pm_region_view2: PersistentMemoryRegionView,
    log_start_addr: nat,
) -> bool 
{
    let pm_bytes1 = pm_region_view1.durable_state;
    let pm_bytes2 = pm_region_view2.durable_state;
    active_metadata_bytes_are_equal(pm_bytes1, pm_bytes2, log_start_addr)
}

pub open spec fn active_metadata_bytes_are_equal(
    bytes1: Seq<u8>,
    bytes2: Seq<u8>,
    log_start_addr: nat
) -> bool 
{
    let cdb1 = spec_check_log_cdb(bytes1, log_start_addr);
    let cdb2 = spec_check_log_cdb(bytes2, log_start_addr);

    &&& cdb1 matches Some(cdb1)
    &&& cdb2 matches Some(cdb2)
    &&& cdb1 == cdb2 
    // this follows from the CDB check but it helps some proofs to state it explicitly
    &&& extract_bytes(bytes1, log_start_addr, u64::spec_size_of()) ==
           extract_bytes(bytes2, log_start_addr, u64::spec_size_of())
    &&& {
        let metadata_pos = spec_get_active_log_metadata_pos(cdb1) + log_start_addr;
        extract_bytes(bytes1, metadata_pos, LogMetadata::spec_size_of() + u64::spec_size_of()) ==
            extract_bytes(bytes2, metadata_pos, LogMetadata::spec_size_of() + u64::spec_size_of())
    }
}

pub open spec fn metadata_types_set(mem: Seq<u8>, log_start_addr: nat) -> bool 
    recommends
        spec_check_log_cdb(mem, log_start_addr) is Some,
        mem.len() >= log_start_addr + spec_log_area_pos()
{
    let cdb = spec_check_log_cdb(mem, log_start_addr).unwrap();
    let metadata_pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
    let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
    let crc_pos =  metadata_pos + LogMetadata::spec_size_of();
    let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
    &&& u64::bytes_parseable(extract_bytes(mem, log_start_addr, u64::spec_size_of()))
    // &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
    &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
    &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
    &&& crc == spec_crc_u64(metadata.spec_to_bytes())
}

pub open spec fn inactive_metadata_types_set(mem: Seq<u8>, log_start_addr: nat) -> bool 
    recommends
        spec_check_log_cdb(mem, log_start_addr) is Some,
        mem.len() >= log_start_addr + spec_log_area_pos()
{
    let cdb = spec_check_log_cdb(mem, log_start_addr).unwrap();
    let metadata_pos = spec_get_inactive_log_metadata_pos(cdb) + log_start_addr;
    let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()));
    let crc_pos =  metadata_pos + LogMetadata::spec_size_of();
    let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
    &&& u64::bytes_parseable(extract_bytes(mem, log_start_addr, u64::spec_size_of()))
    // &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
    &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
    &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
    &&& crc == spec_crc_u64(metadata.spec_to_bytes())
}

pub open spec fn memory_matches_deserialized_cdb(pm_region_view: PersistentMemoryRegionView, log_start_addr: nat, cdb: bool) -> bool
{
    &&& no_outstanding_writes_in_range(pm_region_view, log_start_addr as int, (log_start_addr + u64::spec_size_of()) as int)
    &&& spec_check_log_cdb(pm_region_view.durable_state, log_start_addr) == Some(cdb)
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
//
// `after_flush` -- only consider whether this will hold after
// the next flush
pub open spec fn metadata_consistent_with_info(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    after_flush: bool,
) -> bool
{
    let mem = if after_flush { pm_region_view.read_state } else { pm_region_view.durable_state };
    let read_cdb = spec_check_log_cdb(mem, log_start_addr);
    let log_metadata = spec_get_active_log_metadata(mem, log_start_addr, cdb);
    let log_crc = spec_get_active_log_crc(mem, log_start_addr, cdb);

    // No outstanding writes to the CDB, log metadata, or log metadata CRC
    &&& {
           ||| after_flush
           ||| no_outstanding_writes_in_range(pm_region_view, log_start_addr as int,
                                            (log_start_addr + u64::spec_size_of()) as int)
    }
    // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
    &&& {
           ||| after_flush
           ||| no_outstanding_writes_in_range(pm_region_view,
                                            (log_start_addr + spec_get_active_log_metadata_pos(cdb)) as int,
                                            (log_start_addr + spec_get_active_log_crc_end(cdb)) as int)
    }

    // All the CRCs match
    &&& log_crc == log_metadata.spec_crc()

    // Various fields are valid and match the parameters to this function
    &&& log_metadata.head == info.head
    &&& log_metadata.log_length == info.log_length

    // The memory region is large enough to hold the entirety of the log area
    &&& log_size == spec_log_area_pos() + info.log_area_len
    &&& mem.len() >= log_start_addr + spec_log_area_pos() + info.log_area_len
    &&& log_start_addr + spec_get_active_log_metadata_pos(cdb) + LogMetadata::spec_size_of() <
            log_start_addr + spec_get_active_log_crc_pos(cdb) + u64::spec_size_of() <
            log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= pm_region_view.len()
}

// This invariant says that the log area of the given
// persistent-memory region view is consistent with both the log
// information `info` and the abstract log state `state`. (Or, if
// `after_flush` is true, it means it *will* be consistent after a
// flush that ensures the durable and read states match.) Also, `info`
// satisfies certain invariant properties and is consistent with
// `state`.
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
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    info: LogInfo,
    state: AbstractLogState,
    after_flush: bool,
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
            let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
            &&& 0 <= pos_relative_to_head < info.log_length ==> {
                    &&& pm_region_view.read_state[absolute_addr] == state.log[pos_relative_to_head]
                    &&& {
                           ||| after_flush
                           ||| pm_region_view.read_state[absolute_addr] == pm_region_view.durable_state[absolute_addr]
                       }
                }
            &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                    pm_region_view.read_state[absolute_addr] == state.pending[pos_relative_to_head - info.log_length]
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
        forall |addr: int| #![trigger pm_region_view.durable_state[addr]] #![trigger pm_region_view.read_state[addr]]
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

pub proof fn lemma_log_area_consistent_with_new_info_and_state_advance_head(
    pm_region_view: PersistentMemoryRegionView, 
    log_start_addr: nat,
    log_size: nat,
    new_head: int,
    prev_info: LogInfo,
    info: LogInfo,
    prev_state: AbstractLogState,
    state: AbstractLogState, 
)
    requires 
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, prev_info, prev_state, false),
        state == prev_state.advance_head(new_head),
        // the rest of the precondition is parts of info_consistent_with_log_area that we already know
        // are satisfied
        pm_region_view.len() >= log_start_addr + spec_log_area_pos() + prev_info.log_area_len,
        info.log_area_len == prev_info.log_area_len,
        info.head == new_head,
        info.log_length <= info.log_plus_pending_length <= info.log_area_len,
        ({
            let amount_of_advancement = new_head - prev_info.head;
            let new_head_log_area_offset =
            if amount_of_advancement < prev_info.log_area_len - prev_info.head_log_area_offset {
                amount_of_advancement + prev_info.head_log_area_offset
            }
            else {
                amount_of_advancement - (prev_info.log_area_len - prev_info.head_log_area_offset)
            };
            &&& info.log_length == prev_info.log_length - amount_of_advancement
            &&& info.log_plus_pending_length == prev_info.log_plus_pending_length - amount_of_advancement 
        }),
        info.head_log_area_offset == info.head % info.log_area_len as u128,
        info.head + info.log_plus_pending_length <= u128::MAX,
        state.log.len() == info.log_length,
        state.pending.len() == info.log_plus_pending_length - info.log_length,
        // The forall below is split into two cases to make the proof more stable.
        forall |pos_relative_to_head: int| {
            let log_area_offset =
                #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                info.head_log_area_offset as int,
                                                                info.log_area_len as int);
            let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
            &&& 0 <= pos_relative_to_head < info.log_length ==> {
                   &&& pm_region_view.read_state[absolute_addr] == state.log[pos_relative_to_head]
                   &&& pm_region_view.read_state[absolute_addr] == pm_region_view.durable_state[absolute_addr]
               }
        },
        forall |pos_relative_to_head: int| {
            let log_area_offset =
                #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                info.head_log_area_offset as int,
                                                                info.log_area_len as int);
            let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
            &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                   pm_region_view.read_state[absolute_addr] == state.pending[pos_relative_to_head - info.log_length]
        }
    ensures 
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, true),
{
    lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, log_start_addr,
                                                                     log_size, prev_info);
}

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

// This lemma proves that two sequences of bytes that may contain valid logs, and their log
// subregions are equal, then the sequences recover to the same log. This is obvious
// but the proof is non-trivial because we need to explicitly prove the equality of 
// each relevant subrange.
pub proof fn lemma_same_log_bytes_recover_to_same_state(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    log_start_addr: nat,
    log_size: nat,
    region_size: nat,
)
    requires
        mem1.len() == region_size,
        mem1.len() == mem2.len(),
        extract_bytes(mem1, log_start_addr, log_size) == 
            extract_bytes(mem2, log_start_addr, log_size),
        0 <= log_start_addr,
        log_start_addr + log_size <= region_size,
        spec_log_area_pos() <= log_size,
    ensures
        UntrustedLogImpl::recover(mem1, log_start_addr, log_size) ==
            UntrustedLogImpl::recover(mem2, log_start_addr, log_size)
{
    lemma_establish_extract_bytes_equivalence(mem1, mem2);

    // Proves that the CDBs are the same
    lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr, log_size, u64::spec_size_of());
    let cdb1 = spec_check_log_cdb(mem1, log_start_addr);
    if let Some(cdb1) = cdb1 {
        let metadata_pos = spec_get_active_log_metadata_pos(cdb1); 
            let metadata_pos = spec_get_active_log_metadata_pos(cdb1); 
        let metadata_pos = spec_get_active_log_metadata_pos(cdb1); 
        let crc_pos = metadata_pos + LogMetadata::spec_size_of();
        assert(spec_log_header_area_size() <= spec_log_area_pos()) by {
            reveal(spec_padding_needed);
        }
        // Proves that metadata, CRC, and log area are the same
        lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + metadata_pos,
                                              log_size, LogMetadata::spec_size_of());
        lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + crc_pos,
                                              log_size, u64::spec_size_of());
        lemma_subrange_of_extract_bytes_equal(mem1, log_start_addr, log_start_addr + spec_log_area_pos(),
                                              log_size, (log_size - spec_log_area_pos()) as nat);
    } else {
        // both are None
    }
}

// This predicate describes whether a given log area offset is
// unreachable during recovery (because it's beyond the tail).
//
// Its parameters are:
// `head_log_area_offset` -- the the log offset where the log head is
// `log_area_len` -- the length of the log area
// `log_length` -- the length of the abstract log
// `log_area_offset` -- the log area offet being asked about
pub open spec fn log_area_offset_unreachable_during_recovery(
    head_log_area_offset: int,
    log_area_len: int,
    log_length: int,
    log_area_offset: int,
) -> bool
{
    log_area_offset_to_relative_log_pos(log_area_offset, head_log_area_offset, log_area_len) >= log_length
}

// This lemma establishes that if:
//
// 1) two views `v1` and `v2` only differ in unreachable parts of
// the log area (one that satisfy
// `log_area_offset_unreachable_during_recovery`),
//
// 2) view `v1` satisfies certain invariant properties,
//
// 3) view `v2` can crash into state `crash_state`,
//
// then `crash_state` recovers to the same abstract state as
// `v1.durable_state`. This is useful to know for the following
// reason. `v1` can obviously crash as `v1.durable_state`. So, if we
// know that all possible crash states of `v1` recover to a valid
// state then we know `crash_state` recovers to a valid state.
//
// The parameters to this function are:
//
// `v1` and `v2` -- the two views
// `crash_state` -- the state that `v2` can crash into
// `log_id` -- the ID of the log
// `cdb` -- the current value of the corruption-detecting boolean
// `info` -- the log information
// `state` -- the abstract log state
// `is_writable_absolute_addr` -- a spec predicate describing
// which absolute addresses in the log area may differ between
// `v1` and `v2`.
pub proof fn lemma_if_view_differs_only_in_log_area_parts_not_accessed_by_recovery_then_recover_state_matches(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
    is_writable_absolute_addr: spec_fn(int) -> bool,
)
    requires
        no_outstanding_writes_to_metadata(v1, log_start_addr),
        memory_matches_deserialized_cdb(v1, log_start_addr, cdb),
        metadata_consistent_with_info(v1, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(v1, log_start_addr, log_size, info, state, false),
        log_size == info.log_area_len + spec_log_area_pos(),
        log_start_addr + spec_log_area_pos() + info.log_area_len <= v1.len(),
        v1.len() == v2.len(),
        forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
            &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
            &&& log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                    info.log_area_len as int,
                    info.log_length as int,
                    addr - (log_start_addr + spec_log_area_pos()))
        },
        views_differ_only_where_subregion_allows(v1, v2, log_start_addr + spec_log_area_pos(),
                                                    info.log_area_len as nat, is_writable_absolute_addr),
    ensures
        recover_state(v2.durable_state, log_start_addr, log_size) ==
            recover_state(v1.durable_state, log_start_addr, log_size),
{
    reveal(spec_padding_needed);
    lemma_establish_extract_bytes_equivalence(v2.durable_state, v1.durable_state);
    assert(recover_state(v2.durable_state, log_start_addr, log_size) =~=
           recover_state(v1.durable_state, log_start_addr, log_size));
}

// This lemma proves that if the only bytes that differ between v1 and v2 are in inactive metadata 
// and the unreachable log area, then any crash state of v2 recovers to the same state as v1.
pub proof fn lemma_if_view_differs_only_in_inactive_metadata_and_unreachable_log_area_then_recovery_state_matches(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
    is_writable_absolute_addr: spec_fn(int) -> bool,
)
    requires 
        no_outstanding_writes_to_metadata(v1, log_start_addr),
        memory_matches_deserialized_cdb(v1, log_start_addr, cdb),
        metadata_consistent_with_info(v1, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(v1, log_start_addr, log_size, info, state, false),
        log_size == info.log_area_len + spec_log_area_pos(),
        log_start_addr + spec_log_area_pos() + info.log_area_len <= v1.len(),
        v1.len() == v2.len(),
        ({
            let inactive_metadata_pos = spec_get_inactive_log_metadata_pos(cdb) + log_start_addr;
            let active_metadata_pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
            &&& forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
                    // either the address is in the unreachable log area
                    ||| {
                        &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                        &&& log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                                info.log_area_len as int,
                                info.log_length as int,
                                addr - (log_start_addr + spec_log_area_pos()))
                    }
                    // or it's in the inactive metadata
                    ||| inactive_metadata_pos <= addr <
                           inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
                }
            &&& active_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of() <=
                   log_start_addr + spec_log_area_pos()
            &&& inactive_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of() <=
                   log_start_addr + spec_log_area_pos()
        }),
        views_differ_only_where_subregion_allows(v1, v2, log_start_addr as nat, log_size as nat,
                                                 is_writable_absolute_addr),
    ensures 
        recover_state(v2.durable_state, log_start_addr, log_size) ==
        recover_state(v1.durable_state, log_start_addr, log_size),
{
    broadcast use pmcopy_axioms;
    lemma_establish_extract_bytes_equivalence(v1.durable_state, v2.durable_state);
    assert(views_differ_only_where_subregion_allows(v1, v2, log_start_addr as nat, log_size as nat,
                                                    is_writable_absolute_addr));
    lemma_establish_extract_bytes_equivalence(v2.durable_state, v1.durable_state);
    assert(recover_state(v2.durable_state, log_start_addr, log_size) =~=
           recover_state(v1.durable_state, log_start_addr, log_size));
}

pub proof fn lemma_header_bytes_equal_implies_active_metadata_bytes_equal(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    log_start_addr: nat,
    log_size: nat
)
    requires 
        log_start_addr + spec_log_area_pos() < log_start_addr + log_size <= mem1.len(),
        log_start_addr + spec_log_area_pos() < log_start_addr + log_size <= mem2.len(),
        extract_bytes(mem1, log_start_addr, spec_log_area_pos()) == 
            extract_bytes(mem2, log_start_addr, spec_log_area_pos()),
        spec_check_log_cdb(mem1, log_start_addr) is Some,
        spec_check_log_cdb(mem2, log_start_addr) is Some,
    ensures 
        active_metadata_bytes_are_equal(mem1, mem2, log_start_addr)
{
    assert(spec_log_header_area_size() <= spec_log_area_pos()) by {
        reveal(spec_padding_needed);
    }

    lemma_establish_extract_bytes_equivalence(mem1, mem2);
    lemma_auto_smaller_range_of_seq_is_subrange(mem1);
}

// This lemma proves that if we two PM states have the same bytes in
// the log header and no outstanding writes in that region, and one of
// the states has metadata types set, then the other also has metadata
// types set. This is useful for proving that the metadata types
// invariant holds when appending to the log.
pub proof fn lemma_metadata_matches_implies_metadata_types_set(
    pm1: PersistentMemoryRegionView,
    pm2: PersistentMemoryRegionView,
    log_start_addr: nat,
    cdb: bool
)
    requires
        pm1.valid(),
        pm2.valid(),
        no_outstanding_writes_to_active_metadata(pm1, log_start_addr, cdb),
        no_outstanding_writes_to_active_metadata(pm2, log_start_addr, cdb),
        metadata_types_set(pm1.durable_state, log_start_addr),
        memory_matches_deserialized_cdb(pm1, log_start_addr, cdb),
        active_metadata_is_equal(pm1, pm2, log_start_addr),
        pm1.len() == pm2.len(),
        log_start_addr + spec_log_area_pos() <= pm1.len(),
    ensures 
        metadata_types_set(pm2.durable_state, log_start_addr)
{
    assert(spec_log_header_area_size() <= spec_log_area_pos()) by {
        reveal(spec_padding_needed);
    }

    lemma_active_metadata_bytes_equal_implies_metadata_types_set(pm1.durable_state, pm2.durable_state,
                                                                 log_start_addr, cdb);
}

// This lemma proves that if two sequences have equal active metadata bytes,
// then both either have their metadata types set, or both don't.
pub proof fn lemma_active_metadata_bytes_equal_implies_metadata_types_set(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    log_start_addr: nat,
    cdb: bool
)
    requires 
        mem1.len() == mem2.len(),
        active_metadata_bytes_are_equal(mem1, mem2, log_start_addr),
        ({
            let cdb1 = spec_check_log_cdb(mem1, log_start_addr);
            let cdb2 = spec_check_log_cdb(mem2, log_start_addr);
            &&& cdb1 is Some 
            &&& cdb2 is Some 
            &&& cdb ==> cdb1.unwrap() && cdb2.unwrap()
            &&& !cdb ==> !cdb1.unwrap() && !cdb2.unwrap()
        }),
        log_start_addr + spec_log_area_pos() <= mem1.len(),
    ensures 
        metadata_types_set(mem1, log_start_addr) ==> metadata_types_set(mem2, log_start_addr),
        !metadata_types_set(mem1, log_start_addr) ==> !metadata_types_set(mem2, log_start_addr),
{
    assert(spec_log_header_area_size() <= spec_log_area_pos()) by {
        reveal(spec_padding_needed);
    }
    
    lemma_establish_extract_bytes_equivalence(mem1, mem2);

    // This lemma automatically establishes the relationship between subranges of subranges from the same sequence, 
    // so knowing that the assertions below cover subranges of larger, equal subranges is enough to establish equality
    // (but we have to assert it explicitly to hit the triggers)
    lemma_auto_smaller_range_of_seq_is_subrange(mem1);
}

// This lemma proves that if the log metadata has been properly set up and there are no outstanding writes to 
// metadata, then the metadata_types_set invariant holds after any crash. This is useful when proving the invariant
// after an update that does not touch metadata.
pub proof fn lemma_metadata_set_after_crash(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    cdb: bool
)
    requires 
        no_outstanding_writes_to_active_metadata(pm_region_view, log_start_addr, cdb),
        metadata_types_set(pm_region_view.durable_state, log_start_addr),
        memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb),
    ensures 
        0 <= log_start_addr < log_start_addr + spec_log_area_pos() < pm_region_view.len()
            ==> metadata_types_set(pm_region_view.durable_state, log_start_addr),
{
    reveal(spec_padding_needed);

    let pm_bytes = pm_region_view.durable_state;
    assert(cdb == spec_check_log_cdb(pm_bytes, log_start_addr).unwrap());

    let s = pm_bytes;
    if 0 <= log_start_addr < log_start_addr + spec_log_area_pos() < pm_region_view.len() {
        assert({
            let s_cdb = spec_check_log_cdb(s, log_start_addr).unwrap();
            &&& s_cdb == cdb 
            &&& spec_get_active_log_metadata(s, log_start_addr, s_cdb) ==
                   spec_get_active_log_metadata(pm_bytes, log_start_addr, s_cdb)
            &&& spec_get_active_log_crc(s, log_start_addr, s_cdb) ==
                   spec_get_active_log_crc(pm_bytes, log_start_addr, s_cdb)
        }) by {
            lemma_establish_extract_bytes_equivalence(s, pm_region_view.durable_state);
        }
    }


    let s = pm_region_view.durable_state;
    if 0 <= log_start_addr < log_start_addr + spec_log_area_pos() < s.len() {
        assert(metadata_types_set(s, log_start_addr)) by {
            lemma_establish_extract_bytes_equivalence(s, pm_region_view.durable_state);
        }
    }
}

// This exported lemma proves that, if various invariants hold for
// the given persistent memory region view `pm_region_view` and
// abstract log state `state`, then for any contents `mem`
// the view can recover into, recovery on `mem` will produce
// `state.drop_pending_appends()`.
//
// `pm_region_view` -- the persistent memory region view
// `log_id` -- the ID of the log
// `cdb` -- the current value of the corruption-detecting boolean
// `info` -- the log information
// `state` -- the abstract log state
pub proof fn lemma_invariants_imply_crash_recover_forall(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb),
        metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, false),
        metadata_types_set(pm_region_view.durable_state, log_start_addr),
    ensures
        ({
            let mem = pm_region_view.durable_state;
            &&& recover_cdb(mem, log_start_addr) == Some(cdb)
            &&& recover_state(mem, log_start_addr, log_size) == Some(state.drop_pending_appends())
            &&& metadata_types_set(mem, log_start_addr)
        }),
{
    let mem = pm_region_view.durable_state;
    assert({
                &&& recover_cdb(mem, log_start_addr) == Some(cdb)
                &&& recover_state(mem, log_start_addr, log_size) == Some(state.drop_pending_appends())
                &&& metadata_types_set(mem, log_start_addr)
          }) by
    {
        lemma_invariants_imply_crash_recover(pm_region_view, log_start_addr, log_size, cdb, info, state);
    }
}

// This lemma proves that, if various invariants hold for the
// given persistent-memory region view `pm_region_view` and
// abstract log state `state`, and if that view can crash as
// contents `mem`, then recovery on `mem` will produce
// `state.drop_pending_appends()`.
//
// `pm_region_view` -- the persistent memory region view
// `mem` -- a possible memory contents that `pm_region_view` can crash as
// `log_id` -- the ID of the log
// `cdb` -- the current value of the corruption-detecting boolean
// `info` -- the log information
// `state` -- the abstract multilog state
proof fn lemma_invariants_imply_crash_recover(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb),
        metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, false),
        metadata_types_set(pm_region_view.durable_state, log_start_addr),
    ensures
        ({
            let mem = pm_region_view.durable_state;
            &&& recover_cdb(mem, log_start_addr) == Some(cdb)
            &&& recover_state(mem, log_start_addr, log_size) == Some(state.drop_pending_appends())
            &&& metadata_types_set(mem, log_start_addr)
        }),
{
    // For the CDB, we observe that:
    //
    // (1) there are no outstanding writes, so the crashed-into
    // state `mem` must match the committed state
    // `pm_region_view.durable_state`, and
    //
    // (2) wherever the crashed-into state matches the committed
    // state on a per-byte basis, any `extract_bytes` results will
    // also match.
    //
    // Therefore, since the metadata in `pm_region_view.durable_state`
    // matches `cdb` (per the invariants), the metadata in
    // `mem` must also match `cdb`.

    let mem = pm_region_view.durable_state;
    assert (recover_cdb(mem, log_start_addr) == Some(cdb)) by {
        lemma_establish_extract_bytes_equivalence(mem, pm_region_view.durable_state);
    }

    // Use `lemma_invariants_imply_crash_recover_for_one_log` on
    // each region to establish that recovery works on all the
    // regions.

    assert(recover_given_cdb(mem, log_start_addr, log_size, cdb) == Some(state.drop_pending_appends())) by {
        lemma_invariants_imply_crash_recover_for_one_log(pm_region_view, log_start_addr, log_size, cdb, info, state);
    }

    // Get Z3 to see the equivalence of the recovery
    // result and the desired abstract state by asking it (with
    // `=~=`) to prove that they're piecewise equivalent.

    assert(recover_state(mem, log_start_addr, log_size) =~= Some(state.drop_pending_appends()));

    // Finally, invoke the lemma that proves that metadata types 
    // are still set in crash states

    lemma_metadata_set_after_crash(pm_region_view, log_start_addr, cdb);
}

// This lemma proves that, if various invariants hold for the
// given persistent-memory view `pm_region_view` and abstract log state
// `state`, and if that view can crash as contents `mem`, then
// recovery on `mem` will produce `state.drop_pending_appends()`.
//
// `pm_region_view` -- the view of this persistent-memory region
// `mem` -- a possible memory contents that `pm_region_view` can crash as
// `log_id` -- the ID of the log
// `cdb` -- the current value of the corruption-detecting boolean
// `info` -- the log information
// `state` -- the abstract log state
proof fn lemma_invariants_imply_crash_recover_for_one_log(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        log_start_addr < log_start_addr + log_size <= pm_region_view.len(),
        metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, false),
    ensures
        recover_given_cdb(pm_region_view.durable_state, log_start_addr, log_size, cdb) ==
            Some(state.drop_pending_appends())
{
    let mem = pm_region_view.durable_state;
    broadcast use pmcopy_axioms;

    lemma_establish_extract_bytes_equivalence(mem, pm_region_view.durable_state);

    let active_metadata_pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
    let active_crc_pos = spec_get_active_log_crc_pos(cdb) + log_start_addr;

    // Since there are no outstanding writes to the active metadata, all crash states recover to the same state
    assert(no_outstanding_writes_in_range(pm_region_view, active_metadata_pos as int, LogMetadata::spec_size_of() as int));
    assert(no_outstanding_writes_in_range(pm_region_view, active_crc_pos as int, u64::spec_size_of() as int));

    assert(extract_bytes(pm_region_view.durable_state, active_metadata_pos as nat, LogMetadata::spec_size_of()) ==
        extract_bytes(mem, active_metadata_pos as nat, LogMetadata::spec_size_of()));
    assert(extract_bytes(pm_region_view.durable_state, active_crc_pos as nat, u64::spec_size_of()) ==
        extract_bytes(mem, active_crc_pos as nat, u64::spec_size_of()));

    assert(recover_given_cdb(mem, log_start_addr, log_size, cdb) == Some(state.drop_pending_appends()));
}

// This lemma proves that, if all regions are consistent wrt a new CDB, and then we
// write and flush that CDB, the regions stay consistent with info.
pub proof fn lemma_metadata_consistent_with_info_after_cdb_update(
    old_pm_region_view: PersistentMemoryRegionView,
    new_pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    new_cdb_bytes: Seq<u8>,
    new_cdb: bool,
    info: LogInfo,
)
    requires
        new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
        new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        new_cdb_bytes.len() == u64::spec_size_of(),
        old_pm_region_view.flush_predicted(),
        new_pm_region_view.flush_predicted(),
        log_start_addr + log_size <= old_pm_region_view.len(),
        log_size > u64::spec_size_of(),
        log_start_addr + spec_get_active_log_crc_end(new_cdb) <= old_pm_region_view.len(),
        new_pm_region_view.flush_predicted(),
        new_pm_region_view.read_state == update_bytes(old_pm_region_view.read_state, log_start_addr as int,
                                                      new_cdb_bytes),
        metadata_consistent_with_info(old_pm_region_view, log_start_addr, log_size, new_cdb, info, false),
    ensures
        metadata_consistent_with_info(new_pm_region_view, log_start_addr, log_size, new_cdb, info, false),
{
    broadcast use pmcopy_axioms;
    let old_mem = old_pm_region_view.durable_state;
    let new_mem = new_pm_region_view.durable_state;
    lemma_establish_extract_bytes_equivalence(old_mem, new_mem);
    assert(extract_bytes(new_mem, log_start_addr, u64::spec_size_of()) == new_cdb_bytes);
    assert(metadata_consistent_with_info(new_pm_region_view, log_start_addr, log_size, new_cdb, info, false));
}

pub proof fn lemma_metadata_types_set_after_cdb_update(
    old_pm_region_view: PersistentMemoryRegionView,
    new_pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    new_cdb_bytes: Seq<u8>,
    old_cdb: bool,
)
    requires 
        old_pm_region_view.flush_predicted(),
        new_pm_region_view.flush_predicted(),
        log_start_addr + spec_log_area_pos() <= log_start_addr + log_size <= old_pm_region_view.len(),
        old_pm_region_view.len() == new_pm_region_view.len(),
        log_size >= spec_log_header_area_size(),
        new_cdb_bytes.len() == u64::spec_size_of(),
        new_cdb_bytes == CDB_FALSE.spec_to_bytes() || new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        old_cdb ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
        !old_cdb ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
        new_pm_region_view.flush_predicted(),
        new_pm_region_view.read_state == update_bytes(old_pm_region_view.read_state, log_start_addr as int,
                                                      new_cdb_bytes),
        metadata_types_set(old_pm_region_view.durable_state, log_start_addr),
        inactive_metadata_types_set(old_pm_region_view.durable_state, log_start_addr),
    ensures 
        metadata_types_set(new_pm_region_view.durable_state, log_start_addr)
{
    broadcast use pmcopy_axioms;

    let old_mem = old_pm_region_view.durable_state;
    let new_mem = new_pm_region_view.durable_state;
    lemma_auto_smaller_range_of_seq_is_subrange(old_mem);
    lemma_auto_smaller_range_of_seq_is_subrange(new_mem);
    lemma_establish_extract_bytes_equivalence(old_mem, new_mem);
    assert(extract_bytes(new_mem, log_start_addr, u64::spec_size_of()) == new_cdb_bytes);
}

// This lemma establishes that, if one flushes persistent memory,
// this will maintain various invariants.
//
// `pm_region_view` -- the persistent memory region view
// `log_id` -- the ID of the log
// `cdb` -- the current value of the corruption-detecting boolean
// `info` -- the log information
// `state` -- the abstract log state
pub proof fn lemma_flushing_metadata_maintains_invariants(
    pm_region_view: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat,
    cdb: bool,
    info: LogInfo,
    state: AbstractLogState,
)
    requires
        memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb),
        metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false),
        info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, false),
        metadata_types_set(pm_region_view.durable_state, log_start_addr),
        log_start_addr + spec_log_area_pos() <= pm_region_view.len(),
    ensures
        pm_region_view.flush_predicted() ==> {
            &&& memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb)
            &&& metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false)
            &&& info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, info, state, false)
            &&& metadata_types_set(pm_region_view.read_state, log_start_addr)
        },
{
    assert(spec_log_header_area_size() <= spec_log_area_pos()) by {
        reveal(spec_padding_needed);
    }

    assert(memory_matches_deserialized_cdb(pm_region_view, log_start_addr, cdb)) by {
        assert(extract_bytes(pm_region_view.durable_state, log_start_addr, u64::spec_size_of()) == 
            extract_bytes(pm_region_view.durable_state, log_start_addr, u64::spec_size_of()));
    }

    // To show that all the metadata still matches even after the
    // flush, observe that everywhere the bytes match, any call to
    // `extract_bytes` will also match.

    assert(metadata_consistent_with_info(pm_region_view, log_start_addr, log_size, cdb, info, false)) by {
        lemma_establish_extract_bytes_equivalence(pm_region_view.durable_state, pm_region_view.durable_state);
    }

    // It's trivial to prove that the bytes in the active metadata are
    // unchanged after the flush, so the metadata types are still set.
}

pub open spec fn states_differ_only_in_log_region(
    s1: Seq<u8>,
    s2: Seq<u8>,
    log_start_addr: nat,
    log_size: nat
) -> bool 
{
    forall |addr: int|{
        &&& 0 <= addr < s1.len() 
        &&& s1[addr] != #[trigger] s2[addr] 
    } ==> log_start_addr <= addr < log_start_addr + log_size
}

pub open spec fn views_differ_only_in_log_region(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat
) -> bool 
{
    &&& v1.len() == v2.len()
    &&& forall |addr: int| #![trigger v2.durable_state[addr]] #![trigger v2.read_state[addr]]
           0 <= addr < v1.len() && !(log_start_addr <= addr < log_start_addr + log_size)
           ==> views_match_at_addr(v1, v2, addr)
}

pub proof fn lemma_if_views_differ_only_in_region_then_states_do(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat
)
    requires
        v1.valid(),
        v2.valid(),
        views_differ_only_in_log_region(v1, v2, log_start_addr, log_size),
    ensures
        states_differ_only_in_log_region(v1.durable_state, v2.durable_state, log_start_addr, log_size),
        states_differ_only_in_log_region(v1.read_state, v2.read_state, log_start_addr, log_size),
{
    assert forall |addr: int|{
        &&& 0 <= addr < v1.durable_state.len() 
        &&& v1.durable_state[addr] != #[trigger] v2.durable_state[addr] 
    } implies log_start_addr <= addr < log_start_addr + log_size by {
        assert(!views_match_at_addr(v1, v2, addr));
    }

    assert forall |addr: int|{
        &&& 0 <= addr < v1.read_state.len() 
        &&& v1.read_state[addr] != #[trigger] v2.read_state[addr] 
    } implies log_start_addr <= addr < log_start_addr + log_size by {
        assert(!views_match_at_addr(v1, v2, addr));
    }
}

pub proof fn lemma_if_committed_states_differ_only_in_log_region_and_no_outstanding_writes_then_views_differ_only_in_log_region(
    v1: PersistentMemoryRegionView,
    v2: PersistentMemoryRegionView,
    log_start_addr: nat,
    log_size: nat
)
    requires
        states_differ_only_in_log_region(v1.durable_state, v2.durable_state, log_start_addr, log_size),
        v1.len() == v2.len(),
        v1.flush_predicted(),
        v2.flush_predicted(),
    ensures 
        views_differ_only_in_log_region(v1, v2, log_start_addr, log_size),
{
    let s1 = v1.durable_state;
    let s2 = v2.durable_state;
    assert(v1.len() == s1.len());
    assert(v2.len() == s2.len());

    assert(forall|addr: int| #![trigger v2.durable_state[addr]] #![trigger v2.read_state[addr]]
           0 <= addr < v1.len() && !(log_start_addr <= addr < log_start_addr + log_size) ==>
           views_match_at_addr(v1, v2, addr));
}

pub open spec fn states_differ_only_outside_log_region(
    s1: Seq<u8>,
    s2: Seq<u8>,
    log_start_addr: nat,
    log_size: nat
) -> bool 
{
    forall |addr: int|{
        &&& 0 <= addr < s1.len() 
        &&& s1[addr] != #[trigger] s2[addr] 
    } ==> {
        ||| 0 <= addr < log_start_addr 
        ||| log_start_addr + log_size <= addr < s1.len()
    }
}

pub proof fn lemma_metadata_fits_in_log_header_area()
    ensures 
        forall |cdb: bool| spec_get_active_log_metadata_pos(cdb) + LogMetadata::spec_size_of() + u64::spec_size_of() <=
            spec_log_area_pos(),
        forall |cdb: bool| spec_get_inactive_log_metadata_pos(cdb) + LogMetadata::spec_size_of() + u64::spec_size_of() <=
            spec_log_area_pos(),
{
    broadcast use pmcopy_axioms;
    reveal(spec_padding_needed);
    assert(spec_log_header_pos_cdb_true() + LogMetadata::spec_size_of() + u64::spec_size_of() <=
           spec_log_area_pos()) by (compute_only);
}

}
