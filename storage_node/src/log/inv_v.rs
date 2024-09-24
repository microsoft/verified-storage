//! This file contains functions describing invariants of a
//! `UntrustedLogImpl`, as well as lemmas about those invariants.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
use crate::log::layout_v::*;
use crate::log::logimpl_v::LogInfo;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This invariant says that there are no outstanding writes to any
    // part of the metadata subregion of the persistent-memory region.
    // It's temporarily violated in the middle of various operations,
    // of course, but it's always restored before finishing an
    // operation.
    pub open spec fn no_outstanding_writes_to_metadata(
        pm_region_view: PersistentMemoryRegionView,
    ) -> bool
    {
        no_outstanding_writes_in_range(pm_region_view, ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                       ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    // This invariant is similar to no_outstanding_writes_to_metadata, except that it allows outstanding writes
    // to the inactive log metadata region.
    pub open spec fn no_outstanding_writes_to_active_metadata(
        pm_region_view: PersistentMemoryRegionView,
        cdb: bool,
    ) -> bool 
    {
        // Note that we include the active log metadata's CRC in the region
        let metadata_pos = if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int }
                           else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int };
        &&& no_outstanding_writes_in_range(
            pm_region_view,
            metadata_pos,
            metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()
        )
        &&& no_outstanding_writes_in_range(pm_region_view,
                                         ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                         ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& no_outstanding_writes_in_range(pm_region_view, ABSOLUTE_POS_OF_LOG_CDB as int,
                                         ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
        &&& deserialize_and_check_log_cdb(pm_region_view.read_state) == Some(cdb)
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
        log_id: u128,
        cdb: bool,
        info: LogInfo,
    ) -> bool
    {
        let mem = pm_region_view.read_state;
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        // All the CRCs match
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()

        // Various fields are valid and match the parameters to this function
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len

        // No outstanding writes to global metadata, region metadata, or the log metadata CDB
        &&& no_outstanding_writes_in_range(pm_region_view, ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                         ABSOLUTE_POS_OF_LOG_CDB as int)
        // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
        &&& no_outstanding_writes_in_range(pm_region_view, get_log_metadata_pos(cdb) as int,
                                         get_log_crc_end(cdb) as int)
    }

    // This lemma proves that, if all regions are consistent wrt a new CDB, and then we
    // write and flush that CDB, the regions stay consistent with info.
    pub proof fn lemma_metadata_consistent_with_info_after_cdb_update(
        old_pm_region_view: PersistentMemoryRegionView,
        new_pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        new_cdb_bytes: Seq<u8>,
        new_cdb: bool,
        info: LogInfo,
    )
        requires
            new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
            new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            new_cdb_bytes.len() == u64::spec_size_of(),
            no_outstanding_writes(old_pm_region_view),
            no_outstanding_writes(new_pm_region_view),
            new_pm_region_view.read_state ==
                update_bytes(old_pm_region_view.read_state, ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes),
            metadata_consistent_with_info(old_pm_region_view, log_id, new_cdb, info),
        ensures
            metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info),
    {
        reveal(spec_padding_needed);
        assert(metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info)) by {
            let old_mem = old_pm_region_view.read_state;
            let new_mem = new_pm_region_view.read_state;
            lemma_establish_subrange_equivalence(old_mem, new_mem);
        }
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
                let pmb = log_area_view.read_state[log_area_offset];
                &&& 0 <= pos_relative_to_head < info.log_length ==> {
                      &&& pmb == state.log[pos_relative_to_head]
                      &&& pmb == log_area_view.durable_state[log_area_offset]
                   }
                &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
                       pmb == state.pending[pos_relative_to_head - info.log_length]
            }
    }

    pub open spec fn info_consistent_with_log_area_in_region(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
        &&& info_consistent_with_log_area(
               get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat),
               info,
               state
           )
    }

    pub open spec fn metadata_types_set(mem: Seq<u8>) -> bool 
    {
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_GLOBAL_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_GLOBAL_CRC as int;
            let metadata = GlobalMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         GlobalMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& GlobalMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, GlobalMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let metadata_pos = ABSOLUTE_POS_OF_REGION_METADATA as int;
            let crc_pos = ABSOLUTE_POS_OF_REGION_CRC as int;
            let metadata = RegionMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                         RegionMetadata::spec_size_of()));
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& RegionMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, RegionMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
            let cdb = u64::spec_from_bytes(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()));
            let metadata_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE }
                               else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE };
            let metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, metadata_pos as nat,
                                                                      LogMetadata::spec_size_of()));
            let crc_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                          else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
            let crc = u64::spec_from_bytes(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()));
            &&& u64::bytes_parseable(extract_bytes(mem, cdb_pos as nat, u64::spec_size_of()))
            &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
            &&& LogMetadata::bytes_parseable(extract_bytes(mem, metadata_pos as nat, LogMetadata::spec_size_of()))
            &&& u64::bytes_parseable(extract_bytes(mem, crc_pos as nat, u64::spec_size_of()))
            &&& crc == spec_crc_u64(metadata.spec_to_bytes())
        }
    }

    pub open spec fn inactive_metadata_types_set(mem: Seq<u8>) -> bool 
    {
        let cdb_pos = ABSOLUTE_POS_OF_LOG_CDB as int;
        let cdb = u64::spec_from_bytes(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()));
        let metadata_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int }
                           else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int };
        let metadata =
            LogMetadata::spec_from_bytes(mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()));
        let crc_pos = if cdb == CDB_TRUE { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int }
                      else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int };
        let crc = u64::spec_from_bytes(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()));
        &&& u64::bytes_parseable(mem.subrange(cdb_pos, cdb_pos + u64::spec_size_of()))
        &&& LogMetadata::bytes_parseable(mem.subrange(metadata_pos, metadata_pos + LogMetadata::spec_size_of()))
        &&& u64::bytes_parseable(mem.subrange(crc_pos, crc_pos + u64::spec_size_of()))
        &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
        &&& crc == spec_crc_u64(metadata.spec_to_bytes())
    }

    pub proof fn lemma_addresses_in_log_area_subregion_correspond_to_relative_log_positions(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo
    )
        requires
            pm_region_view.len() == info.log_area_len,
            info.head_log_area_offset < info.log_area_len,
            info.log_area_len > 0,
        ensures
            forall |log_area_offset: int| #![trigger pm_region_view.read_state[log_area_offset]]
                0 <= log_area_offset < info.log_area_len ==> {
                    let pos_relative_to_head =
                        if log_area_offset >= info.head_log_area_offset {
                            log_area_offset - info.head_log_area_offset
                        }
                        else {
                            log_area_offset - info.head_log_area_offset + info.log_area_len
                        };
                    &&& 0 <= pos_relative_to_head < info.log_area_len
                    &&& log_area_offset ==
                           relative_log_pos_to_log_area_offset(pos_relative_to_head, info.head_log_area_offset as int,
                                                               info.log_area_len as int)
                }
    {
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
        info: LogInfo
    )
        requires
            pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len,
            info.head_log_area_offset < info.log_area_len,
            info.log_area_len > 0,
        ensures
            forall |addr: int| #![trigger pm_region_view.read_state[addr]]
                ABSOLUTE_POS_OF_LOG_AREA <= addr < ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len ==> {
                    let log_area_offset = addr - ABSOLUTE_POS_OF_LOG_AREA;
                    let pos_relative_to_head =
                        if log_area_offset >= info.head_log_area_offset {
                            log_area_offset - info.head_log_area_offset
                        }
                        else {
                            log_area_offset - info.head_log_area_offset + info.log_area_len
                        };
                    &&& 0 <= pos_relative_to_head < info.log_area_len
                    &&& addr == ABSOLUTE_POS_OF_LOG_AREA +
                              relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                  info.head_log_area_offset as int,
                                                                  info.log_area_len as int)
                }
    {
    }

    // This lemma proves that, if various invariants hold for the
    // given persistent-memory region view `pm_region_view` and
    // abstract log state `state`, and if that view has durable
    // state `mem`, then recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract multilog state
    pub proof fn lemma_invariants_imply_crash_recover(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.valid(),
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            metadata_types_set(pm_region_view.read_state),
        ensures
            recover_cdb(pm_region_view.durable_state) == Some(cdb),
            recover_state(pm_region_view.durable_state, log_id) == Some(state.drop_pending_appends()),
            metadata_types_set(pm_region_view.durable_state),
    {
        reveal(spec_padding_needed);

        let mem = pm_region_view.durable_state;
        lemma_establish_subrange_equivalence(pm_region_view.read_state, pm_region_view.durable_state);

        // For the CDB, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        // state `mem` must match the committed state
        // `pm_region_view.committed()`, and
        //
        // (2) wherever the crashed-into state matches the committed
        // state on a per-byte basis, any `extract_bytes` results will
        // also match.
        //
        // Therefore, since the metadata in `pm_region_view.committed()`
        // matches `cdb` (per the invariants), the metadata in
        // `mem` must also match `cdb`.

        assert(recover_cdb(mem) =~= Some(cdb));

        // Use `lemma_invariants_imply_crash_recover_for_one_log` on
        // each region to establish that recovery works on all the
        // regions.

        assert(recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())) by {

            // The tricky part is showing that the result of `extract_log` will produce the desired result.
            // Use `=~=` to ask Z3 to prove this equivalence by proving it holds on each byte.

            lemma_establish_subrange_equivalence(mem, pm_region_view.read_state);
            let log_view = get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA as nat, info.log_area_len as nat);
            lemma_addresses_in_log_area_subregion_correspond_to_relative_log_positions(log_view, info);
            assert(recover_log_from_log_area_given_metadata(log_view.durable_state, info.head as int,
                                                            info.log_length as int)
                   =~= Some(state.drop_pending_appends()));
            assert(recover_log(mem, info.log_area_len as int, info.head as int, info.log_length as int)
                   =~= Some(state.drop_pending_appends()));
        }

        // Get Z3 to see the equivalence of the recovery
        // result and the desired abstract state by asking it (with
        // `=~=`) to prove that they're piecewise equivalent.

        assert(recover_state(mem, log_id) =~= Some(state.drop_pending_appends()));
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

    // This lemma establishes that if view `v` satisfies certain
    // invariant properties, and if `mem` differs from
    // `v.durable_state` only in unreachable parts of the log area
    // (one that satisfy
    // `log_area_offset_unreachable_during_recovery`), then `mem`
    // recovers to the same abstract state as `v1.durable_state`. So,
    // if we know that `v1` recovers to a valid state then we know
    // `mem` does as well.
    //
    // The parameters to this function are:
    //
    // `v` and `mem` -- the view and memory described above
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `is_writable_absolute_addr` -- a spec predicate describing
    // which absolute addresses in the log area may differ between
    // `v1.durable_state` and `mem`.
    pub proof fn lemma_if_view_and_memory_differ_only_in_inaccessible_log_area_parts_then_recover_state_matches(
        v: PersistentMemoryRegionView,
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        is_writable_absolute_addr: spec_fn(int) -> bool,
    )
        requires
            v.valid(),
            no_outstanding_writes_to_metadata(v),
            memory_matches_deserialized_cdb(v, cdb),
            metadata_consistent_with_info(v, log_id, cdb, info),
            info_consistent_with_log_area_in_region(v, info, state),
            ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len <= v.len(),
            v.len() == mem.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> 
                  log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                                                              info.log_area_len as int,
                                                              info.log_length as int,
                                                              addr - ABSOLUTE_POS_OF_LOG_AREA),
            memories_differ_only_where_subregion_allows(v.durable_state, mem, ABSOLUTE_POS_OF_LOG_AREA as nat,
                                                        info.log_area_len as nat, is_writable_absolute_addr),
        ensures
            recover_state(mem, log_id) == recover_state(v.durable_state, log_id),
    {
        reveal(spec_padding_needed);
        lemma_establish_subrange_equivalence(mem, v.durable_state);
        lemma_establish_subrange_equivalence(v.read_state, v.durable_state);
        assert(recover_state(mem, log_id) =~= recover_state(v.durable_state, log_id));
    }
}
