//! This file contains functions describing invariants of a
//! `UntrustedMultiLogImpl`, as well as lemmas about those invariants.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!

use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_v::LogInfo;
use crate::multilog::multilogspec_t::{AbstractLogState, AbstractMultiLogState};
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This trivial function indicating whether a given log index is
    // valid is used for triggering numerous `forall` invariants.
    pub open spec fn is_valid_log_index(which_log: u32, num_logs: u32) -> bool
    {
        which_log < num_logs
    }

    // This invariant says that there are no outstanding writes to any
    // part of the metadata subregion of any persistent-memory region.
    // It's temporarily violated in the middle of various operations,
    // of course, but it's always restored before finishing an
    // operation.
    pub open spec fn no_outstanding_writes_to_metadata(
        pm_regions_view: PersistentMemoryRegionsView,
        num_logs: u32,
    ) -> bool
    {
        forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) ==>
           pm_regions_view[which_log as int].no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                                          ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    // This invariant says that there are no outstanding writes to the
    // CDB area of persistent memory, and that the committed contents
    // of that area correspond to the given boolean `cdb`.
    pub open spec fn memory_matches_cdb(pm_regions_view: PersistentMemoryRegionsView, cdb: bool) -> bool
    {
        &&& pm_regions_view.no_outstanding_writes_in_range(0int, ABSOLUTE_POS_OF_LOG_CDB as int,
                                                         ABSOLUTE_POS_OF_LOG_CDB + CRC_SIZE)
        &&& extract_and_parse_log_cdb(pm_regions_view[0].committed()) == Some(cdb)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_regions_view: PersistentMemoryRegionsView, cdb: bool) -> bool
    {
        &&& pm_regions_view.no_outstanding_writes_in_range(0int, ABSOLUTE_POS_OF_LOG_CDB as int,
            ABSOLUTE_POS_OF_LOG_CDB + CRC_SIZE)
        &&& deserialize_and_check_log_cdb(pm_regions_view[0].committed()) == Some(cdb)
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
    // `multilog_id` -- the GUID of the multilog
    //
    // `num_logs` -- the number of logs in the multilog
    //
    // `which_log` -- which of the multilog's logs `pm_region_view` stores
    //
    // `cdb` -- the current boolean value of the corruption-detection
    // boolean
    //
    // `info` -- various variables describing information about this
    // log
    pub open spec fn metadata_consistent_with_info(
        pm_region_view: PersistentMemoryRegionView,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
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
        &&& global_metadata.program_guid == MULTILOG_PROGRAM_GUID
        &&& global_metadata.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == LENGTH_OF_REGION_METADATA
        &&& region_metadata.region_size == mem.len()
        &&& region_metadata.multilog_id == multilog_id
        &&& region_metadata.num_logs == num_logs
        &&& region_metadata.which_log == which_log
        &&& region_metadata.log_area_len == info.log_area_len
        &&& log_metadata.head == info.head
        &&& log_metadata.log_length == info.log_length

        // The memory region is large enough to hold the entirety of the log area
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    }

    // This lemma proves that, if all regions are consistent wrt a new CDB, and then we
    // write and flush that CDB, the regions stay consistent with info.
    pub proof fn lemma_each_metadata_consistent_with_info_after_cdb_update(
        old_pm_region_view: PersistentMemoryRegionsView,
        new_pm_region_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        new_cdb_bytes: Seq<u8>,
        new_cdb: bool,
        infos: Seq<LogInfo>,
    )
        requires
            new_cdb == false ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
            new_cdb == true ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            new_cdb_bytes.len() == CRC_SIZE,
            old_pm_region_view.no_outstanding_writes(),
            new_pm_region_view.no_outstanding_writes(),
            num_logs > 0,
            new_pm_region_view =~= old_pm_region_view.write(0int, ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
            each_metadata_consistent_with_info(old_pm_region_view, multilog_id, num_logs, new_cdb, infos),
        ensures
            each_metadata_consistent_with_info(new_pm_region_view, multilog_id, num_logs, new_cdb, infos),
    {
        // The bytes in non-updated regions are unchanged and remain consistent after updating the CDB.
        assert(forall |w: u32| 1 <= w && #[trigger] is_valid_log_index(w, num_logs) ==>
            old_pm_region_view[w as int].committed() =~= new_pm_region_view[w as int].committed()
        );
        assert(forall |w: u32| 1 <= w && #[trigger] is_valid_log_index(w, num_logs) ==>
            metadata_consistent_with_info(new_pm_region_view[w as int], multilog_id, num_logs, w, new_cdb, infos[w as int])
        );

        // The 0th old region (where the CDB is stored) is consistent with the new CDB; this follows from
        // the precondition.
        assert(is_valid_log_index(0, num_logs));
        assert(metadata_consistent_with_info(old_pm_region_view[0int], multilog_id, num_logs, 0, new_cdb, infos[0int]));

        // The metadata in the updated region is also consistent
        assert(metadata_consistent_with_info(new_pm_region_view[0int], multilog_id, num_logs, 0, new_cdb, infos[0int])) by {
            let old_mem = old_pm_region_view[0int].committed();
            let new_mem = new_pm_region_view[0int].committed();
            lemma_establish_extract_bytes_equivalence(old_mem, new_mem);
        }
    }

    // This invariant says that `metadata_consistent_with_info` holds
    // for each region of the given persistent memory regions view
    // `pm_regions_view`.
    pub open spec fn each_metadata_consistent_with_info(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
    ) -> bool
    {
        &&& pm_regions_view.regions.len() == infos.len() == num_logs > 0
        &&& forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) ==> {
            let w = which_log as int;
            metadata_consistent_with_info(pm_regions_view[w], multilog_id, num_logs, which_log, cdb, infos[w])
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
        pm_region_view: PersistentMemoryRegionView,
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
                let addr = ABSOLUTE_POS_OF_LOG_AREA +
                    #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                   info.head_log_area_offset as int,
                                                                   info.log_area_len as int);
                let pmb = pm_region_view.state[addr];
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

    // This invariant says that `info_consistent_with_log_area` holds
    // for all logs in the multilog.
    pub open spec fn each_info_consistent_with_log_area(
        pm_regions_view: PersistentMemoryRegionsView,
        num_logs: u32,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
    ) -> bool
    {
        &&& pm_regions_view.regions.len() == infos.len() == state.num_logs() == num_logs > 0
        &&& forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) ==> {
           let w = which_log as int;
           info_consistent_with_log_area(pm_regions_view[w], infos[w], state[w])
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
    // trigger used in `info_consistent_with_log_area` and
    // `each_info_consistent_with_log_area`.
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
                              relative_log_pos_to_log_area_offset(pos_relative_to_head, info.head_log_area_offset as int,
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
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `which_log` -- which log this region stores
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    proof fn lemma_invariants_imply_crash_recover_for_one_log(
        pm_region_view: PersistentMemoryRegionView,
        mem: Seq<u8>,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            metadata_consistent_with_info(pm_region_view, multilog_id, num_logs, which_log, cdb, info),
            info_consistent_with_log_area(pm_region_view, info, state),
        ensures
            recover_abstract_log_from_region_given_cdb(mem, multilog_id, num_logs as int, which_log as int, cdb) ==
               Some(state.drop_pending_appends())
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

        assert(extract_log(mem, info.log_area_len as int, info.head as int, info.log_length as int) =~=
               state.drop_pending_appends().log);
    }

    // This lemma proves that, if various invariants hold for the
    // given persistent-memory regions view `pm_regions_view` and
    // abstract multilog state `state`, and if that view can crash as
    // contents `mem`, then recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `mems` -- a possible memory contents that `pm_regions_view` can crash as
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract multilog state
    proof fn lemma_invariants_imply_crash_recover(
        pm_regions_view: PersistentMemoryRegionsView,
        mems: Seq<Seq<u8>>,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
    )
        requires
            pm_regions_view.can_crash_as(mems),
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
        ensures
            recover_all(mems, multilog_id) == Some(state.drop_pending_appends())
    {
        // For the CDB, we observe that:
        //
        // (1) there are no outstanding writes, so the crashed-into
        // state `mems[0]` must match the committed state
        // `pm_regions_view.committed()[0]`, and
        //
        // (2) wherever the crashed-into state matches the committed
        // state on a per-byte basis, any `extract_bytes` results will
        // also match.
        //
        // Therefore, since the metadata in `pm_regions_view.committed()[0]`
        // matches `cdb` (per the invariants), the metadata in
        // `mems[0]` must also match `cdb`.

        assert (recover_cdb(mems[0]) == Some(cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in the invariants
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_regions_view[0]);
            lemma_establish_extract_bytes_equivalence(mems[0], pm_regions_view.committed()[0]);
        }

        // Use `lemma_invariants_imply_crash_recover_for_one_log` on
        // each region to establish that recovery works on all the
        // regions.

        assert forall |which_log: u32| is_valid_log_index(which_log, num_logs) implies
                recover_abstract_log_from_region_given_cdb(
                    #[trigger] mems[which_log as int], multilog_id, mems.len() as int, which_log as int, cdb) ==
                Some(state[which_log as int].drop_pending_appends()) by {
            let w = which_log as int;
            lemma_invariants_imply_crash_recover_for_one_log(pm_regions_view[w], mems[w], multilog_id,
                                                             num_logs, which_log, cdb, infos[w], state[w]);
        }

        // Finally, get Z3 to see the equivalence of the recovery
        // result and the desired abstract state by asking it (with
        // `=~=`) to prove that they're piecewise equivalent.

        assert(recover_all(mems, multilog_id) =~= Some(state.drop_pending_appends()));
    }

    // This exported lemma proves that, if various invariants hold for
    // the given persistent memory regions view `pm_regions_view` and
    // abstract multilog state `state`, then for any contents `mem`
    // the view can recover into, recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract multilog state
    pub proof fn lemma_invariants_imply_crash_recover_forall(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
        ensures
            forall |mem| pm_regions_view.can_crash_as(mem) ==>
                recover_all(mem, multilog_id) == Some(state.drop_pending_appends())
    {
        assert forall |mem| pm_regions_view.can_crash_as(mem) implies recover_all(mem, multilog_id) ==
                   Some(state.drop_pending_appends()) by
        {
            lemma_invariants_imply_crash_recover(pm_regions_view, mem, multilog_id, num_logs, cdb, infos, state);
        }
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract multilog state
    // `which_log` -- region on which the inactive level-3 metadata will be overwritten
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_metadata_maintains_invariants(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
        which_log: u32,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
            is_valid_log_index(which_log, num_logs),
            bytes_to_write.len() == LENGTH_OF_LOG_METADATA,
       ensures
            ({
                let pm_regions_view2 = pm_regions_view.write(which_log as int, get_log_metadata_pos(!cdb) as int,
                                                             bytes_to_write);
                &&& memory_matches_deserialized_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.write(which_log as int, get_log_metadata_pos(!cdb) as int,
                                                     bytes_to_write);
        let w = which_log as int;

        assert(memory_matches_deserialized_cdb(pm_regions_view2, cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in invariants.
            assert(extract_log_cdb(pm_regions_view2[0].committed()) =~=
                   extract_log_cdb(pm_regions_view[0].committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)) by {
            lemma_establish_extract_bytes_equivalence(pm_regions_view[w].committed(), pm_regions_view2[w].committed());
        }
    }

    // This lemma establishes that, if one updates the inactive
    // log metadata in a region, this will maintain various
    // invariants. The "inactive" log metadata is the
    // metadata corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract multilog state
    // `which_log` -- region on which the inactive log metadata will be overwritten
    // `bytes_to_write` -- bytes to be written to the inactive log metadata area
    pub proof fn lemma_updating_inactive_crc_maintains_invariants(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
        which_log: u32,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view, multilog_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
            is_valid_log_index(which_log, num_logs),
            bytes_to_write.len() == CRC_SIZE,
        ensures
            ({
                let pm_regions_view2 = pm_regions_view.write(
                    which_log as int,
                    get_log_metadata_pos(!cdb) + LENGTH_OF_LOG_METADATA,
                    bytes_to_write
                );
                &&& memory_matches_deserialized_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.write(
            which_log as int,
            get_log_metadata_pos(!cdb) + LENGTH_OF_LOG_METADATA,
            bytes_to_write
        );
        let w = which_log as int;

        assert(memory_matches_deserialized_cdb(pm_regions_view2, cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in invariants.
            assert(extract_log_cdb(pm_regions_view2[0].committed()) =~=
                   extract_log_cdb(pm_regions_view[0].committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)) by {
            lemma_establish_extract_bytes_equivalence(pm_regions_view[w].committed(), pm_regions_view2[w].committed());
        }
    }

    // This lemma establishes that, if one flushes persistent memory,
    // this will maintain various invariants.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `multilog_id` -- the ID of the multilog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract multilog state
    pub proof fn lemma_flushing_metadata_maintains_invariants(
        pm_regions_view: PersistentMemoryRegionsView,
        multilog_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractMultiLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view,  multilog_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
       ensures
            ({
                let pm_regions_view2 = pm_regions_view.flush();
                &&& memory_matches_deserialized_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.flush();

        assert(memory_matches_deserialized_cdb(pm_regions_view2, cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in invariants.
            assert(extract_log_cdb(pm_regions_view2[0].committed()) =~=
                   extract_log_cdb(pm_regions_view[0].committed()));
        }

        // To show that all the metadata still matches even after the
        // flush, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) implies {
            metadata_consistent_with_info(pm_regions_view2[which_log as int], multilog_id, num_logs, which_log, cdb,
                                          infos[which_log as int])
        } by {
            lemma_establish_extract_bytes_equivalence(pm_regions_view[which_log as int].committed(),
                                                      pm_regions_view2[which_log as int].committed());
        }
    }

}
