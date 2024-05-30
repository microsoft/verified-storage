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
use crate::pmem::serialization_t::*;
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
        pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                      ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    // This invariant says that there are no outstanding writes to the
    // CDB area of persistent memory, and that the committed contents
    // of that area correspond to the given boolean `cdb`.
    pub open spec fn memory_matches_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB + CRC_SIZE)
        &&& extract_and_parse_log_cdb(pm_region_view.committed()) == Some(cdb)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB + CRC_SIZE)
        &&& deserialize_and_check_log_cdb(pm_region_view.committed()) == Some(cdb)
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
        let mem = pm_region_view.committed();
        let global_metadata = deserialize_global_metadata(mem);
        let global_crc = deserialize_global_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let log_metadata = deserialize_log_metadata(mem, cdb);
        let log_crc = deserialize_log_crc(mem, cdb);

        // No outstanding writes to global metadata, region metadata, or the log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_CDB as int)
        // Also, no outstanding writes to the log metadata corresponding to the active log metadata CDB
        &&& pm_region_view.no_outstanding_writes_in_range(get_log_metadata_pos(cdb) as int,
                                                        get_log_crc_end(cdb) as int)

        // All the CRCs match
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()

        // Various fields are valid and match the parameters to this function
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == LENGTH_OF_REGION_METADATA
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
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
            new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_serialize(),
            new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_serialize(),
            new_cdb_bytes.len() == CRC_SIZE,
            old_pm_region_view.no_outstanding_writes(),
            new_pm_region_view.no_outstanding_writes(),
            new_pm_region_view =~= old_pm_region_view.write(ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
            metadata_consistent_with_info(old_pm_region_view, log_id, new_cdb, info),
        ensures
            metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info),
    {
        assert(metadata_consistent_with_info(new_pm_region_view, log_id, new_cdb, info)) by {
            let old_mem = old_pm_region_view.committed();
            let new_mem = new_pm_region_view.committed();
            lemma_establish_extract_bytes_equivalence(old_mem, new_mem);
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

    pub open spec fn info_consistent_with_log_area_in_region(
        pm_region_view: PersistentMemoryRegionView,
        info: LogInfo,
        state: AbstractLogState,
    ) -> bool
    {
        &&& pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
        &&& info_consistent_with_log_area(
               get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA, info.log_area_len),
               info,
               state
           )
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
            forall |log_area_offset: int| #![trigger pm_region_view.state[log_area_offset]]
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
            forall |addr: int| #![trigger pm_region_view.state[addr]]
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
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
        ensures
            recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())
    {
        // For the metadata, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        //     state `mem` must match the committed state
        //     `pm_region_view.committed()`, and
        // (2) wherever the crashed-into state matches the committed
        //     state on a per-byte basis, any `extract_bytes` results
        //     will also match.
        //
        // Therefore, since the metadata in
        // `pm_region_view.committed()` matches `state` (per the
        // invariants), the metadata in `mem` must also match `state`.

        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
        lemma_establish_extract_bytes_equivalence(mem, pm_region_view.committed());

        // The tricky part is showing that the result of `extract_log` will produce the desired result.
        // Use `=~=` to ask Z3 to prove this equivalence by proving it holds on each byte.

        let log_view = get_subregion_view(pm_region_view, ABSOLUTE_POS_OF_LOG_AREA, info.log_area_len);
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(log_view);
        assert(recover_log_from_log_area_given_metadata(log_view.committed(), info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
        assert(recover_log(mem, info.log_area_len as int, info.head as int, info.log_length as int)
               =~= Some(state.drop_pending_appends()));
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
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
        ensures
            recover_state(mem, log_id) == Some(state.drop_pending_appends())
    {
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

        assert (recover_cdb(mem) == Some(cdb)) by {
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
            lemma_establish_extract_bytes_equivalence(mem, pm_region_view.committed());
        }

        // Use `lemma_invariants_imply_crash_recover_for_one_log` on
        // each region to establish that recovery works on all the
        // regions.

        assert(recover_given_cdb(mem, log_id, cdb) == Some(state.drop_pending_appends())) by {
            lemma_invariants_imply_crash_recover_for_one_log(pm_region_view, mem, log_id, cdb, info, state);
        }

        // Finally, get Z3 to see the equivalence of the recovery
        // result and the desired abstract state by asking it (with
        // `=~=`) to prove that they're piecewise equivalent.

        assert(recover_state(mem, log_id) =~= Some(state.drop_pending_appends()));
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
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
        ensures
            forall |mem| pm_region_view.can_crash_as(mem) ==>
                recover_state(mem, log_id) == Some(state.drop_pending_appends())
    {
        assert forall |mem| pm_region_view.can_crash_as(mem) implies recover_state(mem, log_id) ==
                   Some(state.drop_pending_appends()) by
        {
            lemma_invariants_imply_crash_recover(pm_region_view, mem, log_id, cdb, info, state);
        }
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_metadata_maintains_invariants(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            bytes_to_write.len() == LENGTH_OF_LOG_METADATA,
       ensures
            ({
                let pm_region_view2 = pm_region_view.write(get_log_metadata_pos(!cdb) as int, bytes_to_write);
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
            })
    {
        let pm_region_view2 = pm_region_view.write(get_log_metadata_pos(!cdb) as int, bytes_to_write);

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_extract_bytes_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_region_view` -- the persistent memory region view
    // `log_id` -- the ID of the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_crc_maintains_invariants(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
            bytes_to_write.len() == CRC_SIZE,
        ensures
            ({
                let pm_region_view2 = pm_region_view.write(
                    get_log_metadata_pos(!cdb) + LENGTH_OF_LOG_METADATA,
                    bytes_to_write
                );
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
            })
    {
        let pm_region_view2 = pm_region_view.write(
            get_log_metadata_pos(!cdb) + LENGTH_OF_LOG_METADATA,
            bytes_to_write
        );

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_extract_bytes_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }
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
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view,  log_id, cdb, info),
            info_consistent_with_log_area_in_region(pm_region_view, info, state),
       ensures
            ({
                let pm_region_view2 = pm_region_view.flush();
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)
                &&& info_consistent_with_log_area_in_region(pm_region_view2, info, state)
            })
    {
        let pm_region_view2 = pm_region_view.flush();

        assert(memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            assert(extract_log_cdb(pm_region_view2.committed()) =~=
                   extract_log_cdb(pm_region_view.committed()));
        }

        // To show that all the metadata still matches even after the
        // flush, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(metadata_consistent_with_info(pm_region_view2, log_id, cdb, info)) by {
            lemma_establish_extract_bytes_equivalence(pm_region_view.committed(),
                                                      pm_region_view2.committed());
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
    // `v1.committed()`. This is useful to know for the following
    // reason. `v1` can obviously crash as `v1.committed()`. So, if we
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
        crash_state: Seq<u8>,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        is_writable_absolute_addr: spec_fn(int) -> bool,
    )
        requires
            no_outstanding_writes_to_metadata(v1),
            memory_matches_deserialized_cdb(v1, cdb),
            metadata_consistent_with_info(v1, log_id, cdb, info),
            info_consistent_with_log_area_in_region(v1, info, state),
            ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len <= v1.len(),
            v2.can_crash_as(crash_state),
            v1.len() == v2.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> 
                  log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                                                              info.log_area_len as int,
                                                              info.log_length as int,
                                                              addr - ABSOLUTE_POS_OF_LOG_AREA),
            views_differ_only_where_subregion_allows(v1, v2, ABSOLUTE_POS_OF_LOG_AREA,
                                                     info.log_area_len, is_writable_absolute_addr),
        ensures
            v1.can_crash_as(v1.committed()),
            recover_state(crash_state, log_id) == recover_state(v1.committed(), log_id),
    {
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(v2);
        lemma_establish_extract_bytes_equivalence(crash_state, v1.committed());
        assert(recover_state(crash_state, log_id) =~= recover_state(v1.committed(), log_id));
    }
}
