//! This file contains lemmas about tentatively appending to a log.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::inv_v::*;
use crate::log::layout_v::*;
use crate::log::logimpl_v::LogInfo;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::PersistentMemoryRegionView;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // This lemma establishes useful facts about performing a
    // contiguous write to effect a tentative append:
    //
    // 1) It's permitted because a crash after the write is initiated
    //    doesn't affect the post-recovery abstract state.
    //
    // 2) It maintains invariants, if `info` and `state` are updated
    //    in a certain way.
    //
    // Parameters:
    //
    // `pm_region_view` -- the view of the persistent memory region
    // before the write
    //
    // `log_id` -- the ID of the log stored on that memory
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_info` -- the pre-append `info` value
    //
    // `prev_state` -- the pre-append abstract state
    pub proof fn lemma_tentatively_append(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        bytes_to_append: Seq<u8>,
        cdb: bool,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, prev_info),
            info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
            ({
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                &&& 0 < num_bytes <= max_len_without_wrapping // no wrapping is necessary
                &&& prev_info.log_plus_pending_length + num_bytes <= log_area_len
                &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
            })
        ensures
            ({
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                // This is how you should update `infos`
                let new_infos = LogInfo{
                    log_plus_pending_length: (prev_info.log_plus_pending_length + num_bytes) as u64,
                    ..prev_info
                };
                // This is how you should update `state`
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append);
                &&& metadata_consistent_with_info(pm_region_view, log_id, cdb, new_infos)
                // The write doesn't conflict with any outstanding writes
                &&& pm_region_view.no_outstanding_writes_in_range(write_addr, write_addr + num_bytes)
                &&& memory_matches_deserialized_cdb(pm_region_view2, cdb)
                &&& metadata_consistent_with_info(pm_region_view2, log_id, cdb, new_infos)
                &&& info_consistent_with_log_area(pm_region_view2, new_infos, new_state)
                &&& new_state.drop_pending_appends() == prev_state.drop_pending_appends()
                // After initiating the write, any crash and recovery will enter the abstract state
                // `new_state.drop_pending_appends()`, so as long as that state is permitted the
                // write will be.
                &&& forall |mem| pm_region_view2.can_crash_as(mem) ==>
                      recover_state(mem, log_id) == Some(new_state.drop_pending_appends())
            }),
    {
        let log_area_len = prev_info.log_area_len;
        let new_info = LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
            ..prev_info
        };
        let new_state = prev_state.tentatively_append(bytes_to_append);
        let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append);
        let new_state = prev_state.tentatively_append(bytes_to_append);

        // To prove that the post-write metadata is consistent with
        // `new_info`, we have to reason about the equivalence of
        // extracted byte sequences that match between the old and new
        // metadata regions.

        assert (metadata_consistent_with_info(pm_region_view2, log_id, cdb, new_info)) by {
            lemma_establish_extract_bytes_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }

        // To prove that the post-write CDB is the same as the
        // pre-write CDB, we have to reason about the equivalence of
        // extracted byte sequences that match between the old and new
        // region.

        assert (memory_matches_deserialized_cdb(pm_region_view2, cdb)) by {
            lemma_establish_extract_bytes_equivalence(pm_region_view.committed(), pm_region_view2.committed());
        }

        // We need extensional equality to reason that the old and new
        // abstract states are the same after dropping pending appends.

        assert(new_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // To prove that all crash states after initiating the write
        // are OK, we just have to invoke the following lemma, which
        // requires that our invariants hold.

        lemma_invariants_imply_crash_recover_forall(pm_region_view2, log_id, cdb, new_info, new_state);

        // To prove that there are no outstanding writes in the range
        // where we plan to write, we need to reason about how
        // addresses in the log area correspond to relative log
        // positions. This is because the invariant talks about
        // relative log positions but we're trying to prove something
        // about addresses in the log area (that there are no
        // outstanding writes to certain of them).

        lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, prev_info);
    }

    // This lemma establishes useful facts about performing two
    // contiguous writes, one at the end of the log area and one at
    // the beginning, to effect a tentative append:
    //
    // 1) Each write is permitted because a crash after it's initiated
    // doesn't affect the post-recovery abstract state.
    //
    // 2) The pair of writes maintains invariants, if `infos` and
    // `state` are updated in a certain way.
    //
    // Parameters:
    //
    // `pm_region_view` -- the view of the persistent memory regions
    // before the write
    //
    // `log_id` -- the ID of the log stored on that memory
    //
    // `bytes_to_append` -- what bytes are being tentatively appended
    //
    // `cdb` -- the current corruption-detecting boolean value
    //
    // `prev_info` -- the pre-append `info` value
    //
    // `prev_state` -- the pre-append abstract state
    pub proof fn lemma_tentatively_append_wrapping(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        bytes_to_append: Seq<u8>,
        cdb: bool,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            memory_matches_deserialized_cdb(pm_region_view, cdb),
            metadata_consistent_with_info(pm_region_view, log_id, cdb, prev_info),
            info_consistent_with_log_area(pm_region_view, prev_info, prev_state),
            ({
                let log_area_len = prev_info.log_area_len;
                let num_bytes = bytes_to_append.len();
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                &&& num_bytes > max_len_without_wrapping // wrapping is required
                &&& prev_info.head + prev_info.log_plus_pending_length + num_bytes <= u128::MAX
                &&& num_bytes <= log_area_len - prev_info.log_plus_pending_length
            }),
        ensures
            ({
                let log_area_len = prev_info.log_area_len;
                let max_len_without_wrapping = log_area_len -
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int, log_area_len as int);
                let new_infos = LogInfo{
                    log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
                    ..prev_info
                };
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
                let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                                     bytes_to_append.len() as int);
                let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append_part1);
                let pm_region_view3 = pm_region_view2.write(ABSOLUTE_POS_OF_LOG_AREA as int, bytes_to_append_part2);
                &&& metadata_consistent_with_info(pm_region_view, log_id, cdb, new_infos)
                // The first write doesn't conflict with any outstanding writes
                &&& pm_region_view.no_outstanding_writes_in_range(write_addr,
                                                                 write_addr + bytes_to_append_part1.len())
                // The second write also doesn't conflict with any outstanding writes
                &&& pm_region_view2.no_outstanding_writes_in_range(
                       ABSOLUTE_POS_OF_LOG_AREA as int,
                       ABSOLUTE_POS_OF_LOG_AREA + bytes_to_append_part2.len())
                &&& metadata_consistent_with_info(pm_region_view3, log_id, cdb, new_infos)
                &&& info_consistent_with_log_area(pm_region_view3, new_infos, new_state)
                &&& memory_matches_deserialized_cdb(pm_region_view3, cdb)
                &&& new_state.drop_pending_appends() == prev_state.drop_pending_appends()
                // After initiating the first write, any crash and recovery will enter the abstract
                // state `prev_state.drop_pending_appends()`, so as long as that state is permitted
                // the write will be.
                &&& forall |mem| pm_region_view2.can_crash_as(mem) ==>
                       recover_state(mem, log_id) == Some(prev_state.drop_pending_appends())
                // After initiating the second write, any crash and recovery will enter the abstract
                // state `prev_state.drop_pending_appends()`, so as long as that state is permitted
                // the write will be.
                &&& forall |mem| pm_region_view3.can_crash_as(mem) ==>
                       recover_state(mem, log_id) == Some(prev_state.drop_pending_appends())
            }),
    {
        let log_area_len = prev_info.log_area_len;
        let max_len_without_wrapping = log_area_len -
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int, log_area_len as int);
        let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
        let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                             bytes_to_append.len() as int);
        let intermediate_info = LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + max_len_without_wrapping) as u64,
            ..prev_info
        };
        let intermediate_state = prev_state.tentatively_append(bytes_to_append_part1);
        let new_info = LogInfo{
            log_plus_pending_length: (prev_info.log_plus_pending_length + bytes_to_append.len()) as u64,
            ..prev_info
        };
        let new_state = prev_state.tentatively_append(bytes_to_append);
        let write_addr = ABSOLUTE_POS_OF_LOG_AREA +
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let pm_region_view2 = pm_region_view.write(write_addr, bytes_to_append_part1);
        let pm_region_view3 = pm_region_view2.write(ABSOLUTE_POS_OF_LOG_AREA as int, bytes_to_append_part2);

        // Invoke `lemma_tentatively_append` on each write.

        lemma_tentatively_append(pm_region_view, log_id, bytes_to_append_part1, cdb,
                                 prev_info, prev_state);
        lemma_tentatively_append(pm_region_view2, log_id, bytes_to_append_part2, cdb,
                                 intermediate_info, intermediate_state);

        // Use extensional equality to prove the equivalence of the
        // intermediate abstract state between writes and the previous
        // state, if both drop pending appends.

        assert(intermediate_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // Use extensional equality to prove the equivalence of the new
        // abstract state, which the caller of this lemma cares about, with
        // an update to the intermediate abstract state, which is what the
        // second call to `lemma_tentatively_append` proves things about.

        assert(new_state =~= intermediate_state.tentatively_append(bytes_to_append_part2)) by {
            assert(prev_state.pending + bytes_to_append_part1 + bytes_to_append_part2 =~=
                   prev_state.pending + bytes_to_append);
        }
    }

}
