//! This file contains lemmas about tentatively appending to a log.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log2::{inv_v::*, layout_v::*, logimpl_v::*};
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
            pm_region_view.valid(),
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
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + num_bytes ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                &&& forall|pm_region_view2: PersistentMemoryRegionView|
                       #[trigger] pm_region_view2.can_result_from_write(pm_region_view, absolute_write_addr,
                                                                        bytes_to_append)
                       ==> info_consistent_with_log_area(pm_region_view2, log_start_addr, log_size, new_info, new_state)
            }),
    {
        assume(false); // TODO @jay
        let log_area_len = prev_info.log_area_len;
        let num_bytes = bytes_to_append.len();
        let new_info = prev_info.tentatively_append(num_bytes as u64);
        let new_state = prev_state.tentatively_append(bytes_to_append);
        let write_addr =
            relative_log_pos_to_log_area_offset(prev_info.log_plus_pending_length as int,
                                                prev_info.head_log_area_offset as int,
                                                log_area_len as int);
        let absolute_write_addr = log_start_addr + spec_log_area_pos() + write_addr;

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

        lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, log_start_addr,
                                                                         log_size, prev_info);

        assert forall|pm_region_view2: PersistentMemoryRegionView|
                   #[trigger] pm_region_view2.can_result_from_write(pm_region_view, absolute_write_addr,
                                                                    bytes_to_append)
               implies info_consistent_with_log_area(pm_region_view2, log_start_addr, log_size,
                                                     new_info, new_state) by {
            lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view2, log_start_addr,
                                                                             log_size, new_info);
            assert forall |pos_relative_to_head: int|
                0 <= pos_relative_to_head < new_info.log_length implies {
                    let log_area_offset =
                        #[trigger] relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                                       new_info.head_log_area_offset as int,
                                                                       new_info.log_area_len as int);
                    let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
                    &&& pm_region_view2.read_state[absolute_addr] == new_state.log[pos_relative_to_head]
                    &&& pm_region_view2.read_state[absolute_addr] == pm_region_view2.durable_state[absolute_addr]
                } by {
                let log_area_offset =
                    relative_log_pos_to_log_area_offset(pos_relative_to_head,
                                                        new_info.head_log_area_offset as int,
                                                        new_info.log_area_len as int);
                let absolute_addr = log_start_addr + spec_log_area_pos() + log_area_offset;
                let chunk = absolute_addr / const_persistence_chunk_size();
                assert(chunk_trigger(chunk));
            }
        }
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
            pm_region_view.valid(),
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
                // The first write is only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| write_addr <= log_area_offset < write_addr + bytes_to_append_part1.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // The second write is also only to log area offsets unreachable during recovery
                &&& forall |log_area_offset: int| 0 <= log_area_offset < bytes_to_append_part2.len() ==>
                       log_area_offset_unreachable_during_recovery(prev_info.head_log_area_offset as int,
                                                                   prev_info.log_area_len as int,
                                                                   prev_info.log_length as int,
                                                                   log_area_offset)
                // After the writes, the log area will be consistent with an updated info and state.
                &&& forall|pm_region_view2: PersistentMemoryRegionView, pm_region_view3: PersistentMemoryRegionView|
                       pm_region_view2.can_result_from_write(pm_region_view, absolute_write_addr1,
                                                             bytes_to_append_part1) &&
                       pm_region_view3.can_result_from_write(pm_region_view2, absolute_write_addr2 as int,
                                                             bytes_to_append_part2)
                       ==> info_consistent_with_log_area(pm_region_view3, log_start_addr, log_size, new_info, new_state)
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
        let absolute_write_addr1 = log_start_addr + spec_log_area_pos() + write_addr;
        let absolute_write_addr2 = log_start_addr + spec_log_area_pos();
        let new_info = prev_info.tentatively_append(bytes_to_append.len() as u64);
        let new_state = prev_state.tentatively_append(bytes_to_append);

        // Invoke `lemma_tentatively_append` on each write.

        lemma_tentatively_append(pm_region_view, bytes_to_append_part1, log_start_addr, log_size,
                                 prev_info, prev_state);
        assert forall|pm_region_view2: PersistentMemoryRegionView, pm_region_view3: PersistentMemoryRegionView|
                   pm_region_view2.can_result_from_write(pm_region_view, absolute_write_addr1,
                                                         bytes_to_append_part1) &&
                   pm_region_view3.can_result_from_write(pm_region_view2, absolute_write_addr2 as int,
                                                         bytes_to_append_part2)
                   implies
               info_consistent_with_log_area(pm_region_view3, log_start_addr, log_size, new_info, new_state) by {
            lemma_tentatively_append(pm_region_view2, bytes_to_append_part2, log_start_addr, log_size,
                                     intermediate_info, intermediate_state);
            let write_addr =
                relative_log_pos_to_log_area_offset(intermediate_info.log_plus_pending_length as int,
                                                    intermediate_info.head_log_area_offset as int,
                                                    log_area_len as int);
            let absolute_write_addr = log_start_addr + spec_log_area_pos() + write_addr;
            assert(pm_region_view3.can_result_from_write(pm_region_view2, absolute_write_addr,
                                                         bytes_to_append_part2));
        }
    }

    // This lemma proves that tentative appends do not modify reachable state and thus do not change
    // the possible recovery states. We have to prove this explicitly because `tentative_append` has a 
    // somewhat weak precondition about the states allowed by `perm` to make it easier to use in the op log
    pub proof fn lemma_append_crash_states_do_not_modify_reachable_state(
        old_pm: PersistentMemoryRegionView,
        new_durable_state: Seq<u8>,
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
            metadata_types_set(old_pm.durable_state, log_start_addr),
            new_durable_state.len() == old_pm.len(),
            log_start_addr + spec_log_header_area_size() < log_start_addr + spec_log_area_pos() <= old_pm.len(),
            forall |addr: int| #[trigger] is_writable_absolute_addr(addr) <==> {
                &&& log_start_addr + spec_log_area_pos() <= addr < log_start_addr + spec_log_area_pos() + log_size
                &&& log_area_offset_unreachable_during_recovery(info.head_log_area_offset as int,
                        info.log_area_len as int,
                        info.log_length as int,
                        addr - (log_start_addr + spec_log_area_pos()))
            },
            memories_differ_only_where_subregion_allows(old_pm.durable_state, new_durable_state,
                                                        log_start_addr + spec_log_area_pos(),
                                                        info.log_area_len as nat, is_writable_absolute_addr),
            UntrustedLogImpl::recover(old_pm.durable_state, log_start_addr as nat, log_size as nat) ==
                Some(state.drop_pending_appends())
        ensures 
            UntrustedLogImpl::recover(new_durable_state, log_start_addr as nat, log_size as nat) ==
                Some(state.drop_pending_appends())
    {
        lemma_establish_extract_bytes_equivalence(old_pm.durable_state, new_durable_state);
        assert(recover_state(new_durable_state, log_start_addr as nat, log_size as nat) =~=
               recover_state(old_pm.durable_state, log_start_addr as nat, log_size as nat));
    }
}
