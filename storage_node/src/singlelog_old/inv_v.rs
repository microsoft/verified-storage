//! This file contains functions describing invariants of a
//! `UntrustedLogImpl`, as well as lemmas about those invariants.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use crate::singlelog::layout_v::*;
use crate::singlelog::singlelogimpl_v::LogInfo;
use crate::singlelog::singlelogspec_t::AbstractLogState;
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
           pm_regions_view[which_log as int].no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LEVEL1_METADATA as int,
                                                                          ABSOLUTE_POS_OF_LOG_AREA as int)
    }

    // This invariant says that there are no outstanding writes to the
    // CDB area of persistent memory, and that the committed contents
    // of that area correspond to the given boolean `cdb`.

    pub open spec fn memory_matches_cdb(cdb_region_view: PersistentMemoryRegionView, cdb: bool) -> bool
    {
        &&& cdb_region_view.no_outstanding_writes()
        &&& parse_cdb(cdb_region_view.committed()) == Some(cdb)
    }

    // This invariant says that there are no outstanding writes to the
    // activate metadata subregion of the persistent-memory region
    // (i.e., everything but the log area and the level-3 metadata
    // corresponding to `!cdb`). It also says that that metadata is
    // consistent with the log information in `info` and various other
    // in-memory variables given in parameters. The parameters to this
    // function are:
    //
    // `pm_region_view` -- the current view of the persistent memory region
    //
    // `log_id` -- the GUID of the singlelog
    //
    // `num_logs` -- the number of logs in the singlelog
    //
    // `which_log` -- which of the singlelog's logs `pm_region_view` stores
    //
    // `cdb` -- the current boolean value of the corruption-detection
    // boolean
    //
    // `info` -- various variables describing information about this
    // log
    // TODO: update documentation and make sure this contains
    // everything you need it to
    pub open spec fn metadata_consistent_with_info<S, H>(
        superblock_region_view: PersistentMemoryRegionView,
        header_region_view: PersistentMemoryRegionView,
        log_id: u128,
        cdb: bool,
        info: LogInfo,
    ) -> bool
        where
            S: Sized + Serializable + SuperBlock,
            H: Sized + Serializable + Headers,
    {
        let committed_sb = superblock_region_view.committed();
        let committed_headers = header_region_view.committed();
        let superblock = S::spec_deserialize(committed_sb);
        let headers = H::spec_deserialize(committed_headers);

        &&& superblock_region_view.no_outstanding_writes()
        &&& header_region_view.no_outstanding_writes()

        &&& superblock.valid()
        &&& headers.valid(cdb)
    }

    // pub open spec fn metadata_consistent_with_info(
    //     pm_region_view: PersistentMemoryRegionView,
    //     log_id: u128,
    //     num_logs: u32,
    //     which_log: u32,
    //     cdb: bool,
    //     info: LogInfo,
    // ) -> bool
    // {
    //     let mem = pm_region_view.committed();
    //     let level1_metadata_bytes = extract_level1_metadata(mem);
    //     let level1_crc = extract_level1_crc(mem);
    //     let level2_metadata_bytes = extract_level2_metadata(mem);
    //     let level2_crc = extract_level2_crc(mem);
    //     let level3_metadata_bytes = extract_level3_metadata(mem, cdb);
    //     let level3_crc = extract_level3_crc(mem, cdb);
    //     let level1_metadata = parse_level1_metadata(level1_metadata_bytes);
    //     let level2_metadata = parse_level2_metadata(level2_metadata_bytes);
    //     let level3_metadata = parse_level3_metadata(level3_metadata_bytes);

    //     // No outstanding writes to level-1 metadata, level-2 metadata, or the level-3 CDB
    //     &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LEVEL1_METADATA as int,
    //                                                     ABSOLUTE_POS_OF_LEVEL3_CDB as int)
    //     // Also, no outstanding writes to the level-3 metadata corresponding to the active level-3 CDB
    //     &&& pm_region_view.no_outstanding_writes_in_range(get_level3_metadata_pos(cdb) as int,
    //                                                     get_level3_crc_end(cdb) as int)

    //     // All the CRCs match
    //     &&& level1_crc == spec_crc_bytes(level1_metadata_bytes)
    //     &&& level2_crc == spec_crc_bytes(level2_metadata_bytes)
    //     &&& level3_crc == spec_crc_bytes(level3_metadata_bytes)

    //     // Various fields are valid and match the parameters to this function
    //     &&& level1_metadata.program_guid == MULTILOG_PROGRAM_GUID
    //     &&& level1_metadata.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
    //     &&& level1_metadata.length_of_level2_metadata == LENGTH_OF_LEVEL2_METADATA
    //     &&& level2_metadata.region_size == mem.len()
    //     &&& level2_metadata.log_id == log_id
    //     &&& level2_metadata.num_logs == num_logs
    //     &&& level2_metadata.which_log == which_log
    //     &&& level2_metadata.log_area_len == info.log_area_len
    //     &&& level3_metadata.head == info.head
    //     &&& level3_metadata.log_length == info.log_length

    //     // The memory region is large enough to hold the entirety of the log area
    //     &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + info.log_area_len
    // }

    // This invariant says that `metadata_consistent_with_info` holds
    // for each region of the given persistent memory regions view
    // `pm_regions_view`.
    pub open spec fn each_metadata_consistent_with_info(
        pm_regions_view: PersistentMemoryRegionsView,
        log_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
    ) -> bool
    {
        &&& pm_regions_view.regions.len() == infos.len() == num_logs > 0
        &&& forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) ==> {
            let w = which_log as int;
            metadata_consistent_with_info(pm_regions_view[w], log_id, num_logs, which_log, cdb, infos[w])
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
    // TODO: update documentation

    pub open spec fn info_consistent_with_log_area(
        data_region_view: PersistentMemoryRegionView,
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

        // the log area is consistent with `info` and `state`
        // TODO: not sure exactly how to remove all of the offset management stuff correctly
        &&& forall |pos_relative_to_head: int| {
                let addr = #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                            info.head_log_area_offset as int,
                                                                            info.log_area_len as int);
                // TODO: i'm not entirely sure what is going on here and if this works for the
                // new layout
                let pmb = data_region_view.state[addr];
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


    // pub open spec fn info_consistent_with_log_area(
    //     pm_region_view: PersistentMemoryRegionView,
    //     info: LogInfo,
    //     state: AbstractLogState,
    // ) -> bool
    // {
    //     // `info` satisfies certain invariant properties
    //     &&& info.log_area_len >= MIN_LOG_AREA_SIZE
    //     &&& info.log_length <= info.log_plus_pending_length <= info.log_area_len
    //     &&& info.head_log_area_offset == info.head as int % info.log_area_len as int
    //     &&& info.head + info.log_plus_pending_length <= u128::MAX

    //     // `info` and `state` are consistent with each other
    //     &&& state.log.len() == info.log_length
    //     &&& state.pending.len() == info.log_plus_pending_length - info.log_length
    //     &&& state.head == info.head
    //     &&& state.capacity == info.log_area_len

    //     // The log area is consistent with `info` and `state`
    //     &&& forall |pos_relative_to_head: int| {
    //             let addr = ABSOLUTE_POS_OF_LOG_AREA +
    //                 #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
    //                                                                info.head_log_area_offset as int,
    //                                                                info.log_area_len as int);
    //             let pmb = pm_region_view.state[addr];
    //             &&& 0 <= pos_relative_to_head < info.log_length ==> {
    //                   &&& pmb.state_at_last_flush == state.log[pos_relative_to_head]
    //                   &&& pmb.outstanding_write.is_none()
    //                }
    //             &&& info.log_length <= pos_relative_to_head < info.log_plus_pending_length ==>
    //                    pmb.flush_byte() == state.pending[pos_relative_to_head - info.log_length]
    //             &&& info.log_plus_pending_length <= pos_relative_to_head < info.log_area_len ==>
    //                    pmb.outstanding_write.is_none()
    //         }
    // }

    // // This invariant says that `info_consistent_with_log_area` holds
    // // for all logs in the singlelog.
    // pub open spec fn each_info_consistent_with_log_area(
    //     pm_regions_view: PersistentMemoryRegionsView,
    //     num_logs: u32,
    //     infos: Seq<LogInfo>,
    //     state: AbstractLogState,
    // ) -> bool
    // {
    //     &&& pm_regions_view.regions.len() == infos.len() == state.num_logs() == num_logs > 0
    //     &&& forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) ==> {
    //        let w = which_log as int;
    //        info_consistent_with_log_area(pm_regions_view[w], infos[w], state[w])
    //     }
    // }

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
    // `log_id` -- the ID of the singlelog
    // `num_logs` -- the number of logs
    // `which_log` -- which log this region stores
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract log state
    proof fn lemma_invariants_imply_crash_recover_for_one_log(
        pm_region_view: PersistentMemoryRegionView,
        mem: Seq<u8>,
        log_id: u128,
        num_logs: u32,
        which_log: u32,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            pm_region_view.can_crash_as(mem),
            metadata_consistent_with_info(pm_region_view, log_id, num_logs, which_log, cdb, info),
            info_consistent_with_log_area(pm_region_view, info, state),
        ensures
            recover_abstract_log_from_region_given_cdb(mem, log_id, num_logs as int, which_log as int, cdb) ==
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
    // abstract singlelog state `state`, and if that view can crash as
    // contents `mem`, then recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `mems` -- a possible memory contents that `pm_regions_view` can crash as
    // `log_id` -- the ID of the singlelog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract singlelog state
    proof fn lemma_invariants_imply_crash_recover<S,H>(
        // pm_regions_view: PersistentMemoryRegionsView,
        superblock_region_view: PersistentMemoryRegionView,
        cdb_region_view: PersistentMemoryRegionView,
        header_region_view: PersistentMemoryRegionView,
        data_region_view: PersistentMemoryRegionView,
        // mems: Seq<Seq<u8>>,
        superblock_mem: Seq<u8>,
        cdb_mem: Seq<u8>,
        header_mem: Seq<u8>,
        data_mem: Seq<u8>,
        log_id: u128,
        // num_logs: u32,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            // pm_regions_view.can_crash_as(mems),
            superblock_region_view.can_crash_as(superblock_mem),
            cdb_region_view.can_crash_as(cdb_mem),
            header_region_view.can_crash_as(header_mem),
            data_region_view.can_crash_as(data_mem),
            memory_matches_cdb(cdb_region_view, cdb),
            // each_metadata_consistent_with_info(pm_regions_view, log_id, num_logs, cdb, infos),
            metadata_consistent_with_info::<S, H>(superblock_region_view, header_region_view, log_id, cdb, info),
            info_consistent_with_log_area(data_region_view, info, state),
            // each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
        ensures
            recover_all(superblock_mem, cdb_mem, header_mem, data_mem, log_id) == Some(state.drop_pending_appends())
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

        assert (recover_cdb(cdb_mem) == Some(cdb)) by {
            // assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in the invariants
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(cdb_region_view);
            lemma_establish_extract_bytes_equivalence(cdb_mem, cdb_region_view.committed());
        }

        // Use `lemma_invariants_imply_crash_recover_for_one_log` on
        // each region to establish that recovery works on all the
        // regions.

        // TODO: replace with something
        // assert forall |which_log: u32| is_valid_log_index(which_log, num_logs) implies
        //         recover_abstract_log_from_region_given_cdb(
        //             #[trigger] mems[which_log as int], log_id, mems.len() as int, which_log as int, cdb) ==
        //         Some(state[which_log as int].drop_pending_appends()) by {
        //     let w = which_log as int;
        //     lemma_invariants_imply_crash_recover_for_one_log(pm_regions_view[w], mems[w], log_id,
        //                                                      num_logs, which_log, cdb, infos[w], state[w]);
        // }

        // Finally, get Z3 to see the equivalence of the recovery
        // result and the desired abstract state by asking it (with
        // `=~=`) to prove that they're piecewise equivalent.

        assert(recover_all(superblock_mem, cdb_mem, header_mem, data_mem, log_id) == Some(state.drop_pending_appends()));
    }

    // This exported lemma proves that, if various invariants hold for
    // the given persistent memory regions view `pm_regions_view` and
    // abstract singlelog state `state`, then for any contents `mem`
    // the view can recover into, recovery on `mem` will produce
    // `state.drop_pending_appends()`.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `log_id` -- the ID of the singlelog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract singlelog state
    pub proof fn lemma_invariants_imply_crash_recover_forall(
        // pm_regions_view: PersistentMemoryRegionsView,
        superblock_region_view: PersistentMemoryRegionView,
        cdb_region_view: PersistentMemoryRegionView,
        header_region_view: PersistentMemoryRegionView,
        data_region_view: PersistentMemoryRegionView,
        log_id: u128,
        // num_logs: u32,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
    )
        requires
            memory_matches_cdb(cdb_region_view, cdb),
            // each_metadata_consistent_with_info(pm_regions_view, log_id, num_logs, cdb, infos),
            metadata_consistent_with_info(superblock_region_view, header_region_view, cdb, info),
            // each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
            info_consistent_with_log_area(data_region_view, info, state),
        ensures
            forall |sb_mem, cdb_mem, h_mem, d_mem|
            {
                &&& superblock_region_view.can_crash_as(sb_mem)
                &&& cdb_region_view.can_crash_as(cdb_mem)
                &&& header_region_view.can_crash_as(h_mem)
                &&& data_region_view.can_crash_as(d_mem)
            } ==> {
                recover_all(sb_mem, cdb_mem, h_mem, d_mem, log_id) == Some(state.drop_pending_appends())
            }
            // forall |mem| pm_regions_view.can_crash_as(mem) ==>
            //     recover_all(mem, log_id) == Some(state.drop_pending_appends())
    {
        // assert forall |mem| pm_regions_view.can_crash_as(mem) implies recover_all(mem, log_id) ==
        //            Some(state.drop_pending_appends()) by
        // {
        //     lemma_invariants_imply_crash_recover(pm_regions_view, mem, log_id, num_logs, cdb, infos, state);
        // }

        assert forall |sb_mem, cdb_mem, h_mem, d_mem|
        {
            &&& superblock_region_view.can_crash_as(sb_mem)
            &&& cdb_region_view.can_crash_as(cdb_mem)
            &&& header_region_view.can_crash_as(h_mem)
            &&& data_region_view.can_crash_as(d_mem)
        } implies {
            recover_all(sb_mem, cdb_mem, h_mem, d_mem, log_id) == Some(state.drop_pending_appends())
        } by {
            lemma_invariants_imply_crash_recover(
                superblock_region_view,
                cdb_region_view,
                header_region_view,
                data_region_view,
                sb_mem,
                cdb_mem,
                h_mem,
                d_mem,
                log_id,
                cdb,
                info,
                state
            );
        }
    }

    // This lemma establishes that, if one updates the inactive
    // level-3 metadata+CRC in a region, this will maintain various
    // invariants. The "inactive" level-3 metadata+CRC is the
    // metadata+CRC corresponding to the negation of the current
    // corruption-detecting boolean.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `log_id` -- the ID of the singlelog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract singlelog state
    // `which_log` -- region on which the inactive level-3 metadata+CRC will be overwritten
    // `bytes_to_write` -- bytes to be written to the inactive level-3 metadata+CRC area
    pub proof fn lemma_updating_inactive_metadata_maintains_invariants(
        // pm_regions_view: PersistentMemoryRegionsView,
        superblock_region_view: PersistentMemoryRegionView,
        cdb_region_view: PersistentMemoryRegionView,
        header_region_view: PersistentMemoryRegionView,
        data_region_view: PersistentMemoryRegionView,
        log_id: u128,
        // num_logs: u32,
        cdb: bool,
        info: LogInfo,
        state: AbstractLogState,
        // which_log: u32,
        bytes_to_write: Seq<u8>,
    )
        requires
            memory_matches_cdb(cdb_region_view, cdb),
            // each_metadata_consistent_with_info(pm_regions_view, log_id, num_logs, cdb, infos),
            metadata_consistent_with_info(superblock_region_view, header_region_view, cdb, info),
            // each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
            info_consistent_with_log_area(data_region_view, info, state),
            // is_valid_log_index(which_log, num_logs),
            bytes_to_write.len() <= LENGTH_OF_LEVEL3_METADATA + CRC_SIZE,
       ensures
            ({
                let pm_regions_view2 = pm_regions_view.write(which_log as int, get_level3_metadata_pos(!cdb) as int,
                                                             bytes_to_write);
                &&& memory_matches_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, log_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.write(which_log as int, get_level3_metadata_pos(!cdb) as int,
                                                     bytes_to_write);
        let w = which_log as int;

        assert(memory_matches_cdb(pm_regions_view2, cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in invariants.
            assert(extract_level3_cdb(pm_regions_view2[0].committed()) =~=
                   extract_level3_cdb(pm_regions_view[0].committed()));
        }

        // To show that all the metadata still matches even after the
        // write, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert(each_metadata_consistent_with_info(pm_regions_view2, log_id, num_logs, cdb, infos)) by {
            lemma_establish_extract_bytes_equivalence(pm_regions_view[w].committed(), pm_regions_view2[w].committed());
        }
    }

    // This lemma establishes that, if one flushes persistent memory,
    // this will maintain various invariants.
    //
    // `pm_regions_view` -- the persistent memory regions view
    // `log_id` -- the ID of the singlelog
    // `num_logs` -- the number of logs
    // `cdb` -- the current value of the corruption-detecting boolean
    // `infos` -- the log information
    // `state` -- the abstract singlelog state
    pub proof fn lemma_flushing_metadata_maintains_invariants(
        pm_regions_view: PersistentMemoryRegionsView,
        log_id: u128,
        num_logs: u32,
        cdb: bool,
        infos: Seq<LogInfo>,
        state: AbstractLogState,
    )
        requires
            memory_matches_cdb(pm_regions_view, cdb),
            each_metadata_consistent_with_info(pm_regions_view,  log_id, num_logs, cdb, infos),
            each_info_consistent_with_log_area(pm_regions_view, num_logs, infos, state),
       ensures
            ({
                let pm_regions_view2 = pm_regions_view.flush();
                &&& memory_matches_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, log_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.flush();

        assert(memory_matches_cdb(pm_regions_view2, cdb)) by {
            assert(is_valid_log_index(0, num_logs)); // This triggers various `forall`s in invariants.
            assert(extract_level3_cdb(pm_regions_view2[0].committed()) =~=
                   extract_level3_cdb(pm_regions_view[0].committed()));
        }

        // To show that all the metadata still matches even after the
        // flush, observe that everywhere the bytes match, any call to
        // `extract_bytes` will also match.

        assert forall |which_log: u32| #[trigger] is_valid_log_index(which_log, num_logs) implies {
            metadata_consistent_with_info(pm_regions_view2[which_log as int], log_id, num_logs, which_log, cdb,
                                          infos[which_log as int])
        } by {
            lemma_establish_extract_bytes_equivalence(pm_regions_view[which_log as int].committed(),
                                                      pm_regions_view2[which_log as int].committed());
        }
    }

}
