//! This file contains lemmas about tentatively appending to a log.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log2::{inv_v::*, layout_v::*, logimpl_v::*, logspec_t::*};
use crate::pmem::{pmemutil_v::*, subregion_v::*, pmemspec_t::*, pmcopy_t::*};
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    // This lemma establishes useful facts about performing a
    // contiguous write to effect a tentative append:
    //
    // 1) The write is permitted because, for each address written to,
    //    there's no outstanding write and it's unreachable during
    //    recovery.
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
        bytes_to_append: Seq<u8>,
        log_start_addr: nat,
        log_size: nat,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            pm_region_view.len() >= log_start_addr + spec_log_area_pos() + prev_info.log_area_len,
            log_size == prev_info.log_area_len + spec_log_area_pos(),
            info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, prev_info, prev_state),
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
                // This is how you should update `infos`
                let new_info = prev_info.tentatively_append(num_bytes as u64);
                // This is how you should update `state`
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let write_addr =
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let absolute_write_addr = log_start_addr + spec_log_area_pos() + write_addr;
                let pm_region_view2 = pm_region_view.write(absolute_write_addr, bytes_to_append);
                &&& pm_region_view.no_outstanding_writes_in_range(absolute_write_addr, absolute_write_addr + num_bytes)
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + num_bytes ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                &&& info_consistent_with_log_area(pm_region_view2, log_start_addr, log_size, new_info, new_state)
            }),
    {
        let new_state = prev_state.tentatively_append(bytes_to_append);

        // We need extensional equality to reason that the old and new
        // abstract states are the same after dropping pending appends.

        assert(new_state.drop_pending_appends() =~= prev_state.drop_pending_appends());

        // To prove that there are no outstanding writes in the range
        // where we plan to write, we need to reason about how
        // addresses in the log area correspond to relative log
        // positions. This is because the invariant talks about
        // relative log positions but we're trying to prove something
        // about addresses in the log area (that there are no
        // outstanding writes to certain of them).

        lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, log_start_addr, log_size, prev_info);
    }

    // This lemma establishes useful facts about performing two
    // contiguous writes, one at the end of the log area and one at
    // the beginning, to effect a tentative append:
    //
    // 1) Each write is permitted because there are no outstanding writes
    //    to the range of addresses to write to.
    //
    // 2) The pair of writes maintains invariants, if `infos` and
    //    `state` are updated in a certain way.
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
        bytes_to_append: Seq<u8>,
        log_start_addr: nat,
        log_size: nat,
        prev_info: LogInfo,
        prev_state: AbstractLogState,
    )
        requires
            pm_region_view.len() >= log_start_addr + spec_log_area_pos() + prev_info.log_area_len,
            log_size == prev_info.log_area_len + spec_log_area_pos(),
            info_consistent_with_log_area(pm_region_view, log_start_addr, log_size, prev_info, prev_state),
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
                let new_info = prev_info.tentatively_append(bytes_to_append.len() as u64);
                let new_state = prev_state.tentatively_append(bytes_to_append);
                let bytes_to_append_part1 = bytes_to_append.subrange(0, max_len_without_wrapping as int);
                let bytes_to_append_part2 = bytes_to_append.subrange(max_len_without_wrapping as int,
                                                                     bytes_to_append.len() as int);
                let write_addr =
                    relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                        prev_info.head_log_area_offset as int,
                                                        log_area_len as int);
                let absolute_write_addr1 = log_start_addr + spec_log_area_pos() + write_addr;
                let absolute_write_addr2 = log_start_addr + spec_log_area_pos();
                let pm_region_view2 = pm_region_view.write(absolute_write_addr1, bytes_to_append_part1);
                let pm_region_view3 = pm_region_view2.write(absolute_write_addr2 as int, bytes_to_append_part2);
                // The first write doesn't conflict with any outstanding writes
                &&& pm_region_view.no_outstanding_writes_in_range(absolute_write_addr1, absolute_write_addr1 + bytes_to_append_part1.len())
                // The first write is only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + bytes_to_append_part1.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // The second write also doesn't conflict with any outstanding writes
                &&& pm_region_view2.no_outstanding_writes_in_range(absolute_write_addr2 as int, log_start_addr + spec_log_area_pos() + bytes_to_append_part2.len() as int)
                // The second write is also only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| 0 <= log_area_offset < bytes_to_append_part2.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // After the writes, the log area will be consistent with an updated info and state.
                &&& info_consistent_with_log_area(pm_region_view3, log_start_addr, log_size, new_info, new_state)
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
        let new_state = prev_state.tentatively_append(bytes_to_append);
        let write_addr =
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let absolute_write_addr = log_start_addr + spec_log_area_pos() + write_addr;
        let pm_region_view2 = pm_region_view.write(absolute_write_addr, bytes_to_append_part1);

        // Invoke `lemma_tentatively_append` on each write.

        lemma_tentatively_append(pm_region_view, bytes_to_append_part1, log_start_addr, log_size, prev_info, prev_state);
        lemma_tentatively_append(pm_region_view2, bytes_to_append_part2, log_start_addr, log_size, intermediate_info, intermediate_state);
    }

    // This lemma proves that tentative appends do not modify reachable state and thus do not change
    // the possible recovery states. We have to prove this explicitly because `tentative_append` has a 
    // somewhat weak precondition about the states allowed by `perm` to make it easier to use in the op log
    pub proof fn lemma_append_crash_states_do_not_modify_reachable_state(
        old_pm: PersistentMemoryRegionView,
        new_pm: PersistentMemoryRegionView,
        log_start_addr: nat,
        log_size: nat,
        info: LogInfo,
        state: AbstractLogState,
        cdb: bool,
        is_writable_absolute_addr: spec_fn(int) -> bool
    )
        requires 
            no_outstanding_writes_to_metadata(old_pm, log_start_addr),
            memory_matches_deserialized_cdb(old_pm, log_start_addr, cdb),
            metadata_consistent_with_info(old_pm, log_start_addr, log_size, cdb, info),
            info_consistent_with_log_area(old_pm, log_start_addr, log_size, info, state),
            metadata_types_set(old_pm.committed(), log_start_addr),
            old_pm.len() == new_pm.len(),
            log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos() <= old_pm.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
                &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                &&& log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                        info.log_area_len as int,
                        info.log_length as int,
                        addr - (log_start_addr + spec_log_area_pos()))
            },
            views_differ_only_where_subregion_allows(old_pm, new_pm, log_start_addr + spec_log_area_pos(),
                                                        info.log_area_len as nat, is_writable_absolute_addr),
            forall |s| #[trigger] old_pm.can_crash_as(s) ==> 
                UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(state.drop_pending_appends())
        ensures 
            forall |s| #[trigger] new_pm.can_crash_as(s) ==> 
                UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(state.drop_pending_appends())
    {
        assert forall |s| #[trigger] new_pm.can_crash_as(s) implies 
            UntrustedLogImpl::recover(s, log_start_addr as nat, log_size as nat) == Some(state.drop_pending_appends())
        by {
            lemma_establish_extract_bytes_equivalence(old_pm.committed(), new_pm.committed());
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(new_pm);
            
            assert(extract_bytes(s, log_start_addr as nat, spec_log_area_pos()) == 
                extract_bytes(new_pm.committed(), log_start_addr as nat, spec_log_area_pos()));
            assert(extract_bytes(s, log_start_addr as nat, u64::spec_size_of()) == 
                extract_bytes(new_pm.committed(), log_start_addr as nat, u64::spec_size_of()));
            lemma_header_bytes_equal_implies_active_metadata_bytes_equal(new_pm.committed(), s, log_start_addr as nat, log_size as nat);
            lemma_active_metadata_bytes_equal_implies_metadata_types_set(new_pm.committed(), s, log_start_addr as nat, cdb);

            lemma_if_view_differs_only_in_log_area_parts_not_accessed_by_recovery_then_recover_state_matches(
                old_pm, new_pm, s, log_start_addr as nat, log_size as nat, cdb, info, state, is_writable_absolute_addr);
        }   
    }
}