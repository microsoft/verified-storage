//! This file contains the implementation of `UntrustedLogImpl`,
//! which implements a provably correct log.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::append_v::*;
use crate::log::inv_v::*;
use crate::log::layout_v::*;
use crate::log::logimpl_t::*;
use crate::log::logspec_t::AbstractLogState;
use crate::log::setup_v::write_setup_metadata;
use crate::log::start_v::{read_cdb, read_log_variables};
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

    // This structure, `LogInfo`, is used by `UntrustedLogImpl`
    // to store information about a single log. Its fields are:
    //
    // `log_area_len` -- how many bytes are in the log area on
    //     persistent memory
    //
    // `head` -- the logical position of the log's head
    //
    // `head_log_area_offset` -- the offset into the log area
    //     holding the byte at the head position. This is
    //     always equal to `head % log_area_len`, and is
    //     cached in this variable to avoid expensive modulo
    //     operations.
    //
    // `log_length` -- the number of bytes in the log beyond the head
    //
    // `log_plus_pending_length` -- the number of bytes in the log and
    //     the pending appends to the log combined
    pub struct LogInfo {
        pub log_area_len: u64,
        pub head: u128,
        pub head_log_area_offset: u64,
        pub log_length: u64,
        pub log_plus_pending_length: u64,
    }

    // This structure, `UntrustedLogImpl`, implements a
    // log. Its fields are:
    //
    // `num_logs` -- the number of logs in the log
    // `cdb` -- the current value of the corruption-detecting boolean
    // `info` -- the log information
    // `state` -- the abstract view of the log
    pub struct UntrustedLogImpl {
        cdb: bool,
        info: LogInfo,
        state: Ghost<AbstractLogState>,
    }

    impl UntrustedLogImpl
    {
        // This static function specifies how multiple regions'
        // contents should be viewed upon recovery as an abstract
        // log state.
        pub closed spec fn recover(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState>
        {
            recover_state(mem, log_id)
        }

        // This method specifies an invariant on `self` that all
        // `UntrustedLogImpl` methods maintain. It requires this
        // invariant to hold on any method invocation, and ensures it
        // in any method invocation that takes `&mut self`.
        //
        // Most of the conjuncts in this invariant are defined in the
        // file `inv_v.rs`. See that file for detailed explanations.
        pub closed spec fn inv<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            log_id: u128,
        ) -> bool
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
        {
            &&& wrpm_region.inv() // whatever the persistent memory regions require as an invariant
            &&& no_outstanding_writes_to_metadata(wrpm_region@)
            &&& memory_matches_deserialized_cdb(wrpm_region@, self.cdb)
            &&& metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, self.info)
            &&& info_consistent_with_log_area(wrpm_region@, self.info, self.state@)
            &&& can_only_crash_as_state(wrpm_region@, log_id, self.state@.drop_pending_appends())
        }

        pub proof fn lemma_inv_implies_wrpm_inv<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            log_id: u128
        )
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
            requires
                self.inv(wrpm_region, log_id)
            ensures
                wrpm_region.inv()
        {}

        pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            log_id: u128
        )
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
            requires
                self.inv(wrpm_region, log_id)
            ensures
                can_only_crash_as_state(wrpm_region@, log_id, self@.drop_pending_appends())
        {}

        // This function specifies how to view the in-memory state of
        // `self` as an abstract log state.
        pub closed spec fn view(&self) -> AbstractLogState
        {
            self.state@
        }

        // The `setup` method sets up persistent memory objects `pm_region`
        // to store an initial empty log. It returns the capacity of the log.
        // See `README.md` for more documentation.
        pub exec fn setup<PMRegion>(
            pm_region: &mut PMRegion,
            log_id: u128,
        ) -> (result: Result<u64, LogErr>)
            where
                PMRegion: PersistentMemoryRegion
            requires
                old(pm_region).inv(),
            ensures
                pm_region.inv(),
                pm_region.constants() == old(pm_region).constants(),
                pm_region@.no_outstanding_writes(),
                match result {
                    Ok(log_capacity) => {
                        let state = AbstractLogState::initialize(log_capacity as int);
                        &&& log_capacity@ <= pm_region@.len()
                        &&& pm_region@.len() == old(pm_region)@.len()
                        &&& can_only_crash_as_state(pm_region@, log_id, state)
                        &&& Self::recover(pm_region@.committed(), log_id) == Some(state)
                        &&& Self::recover(pm_region@.flush().committed(), log_id) == Some(state)
                        &&& state == state.drop_pending_appends()
                    },
                    Err(LogErr::InsufficientSpaceForSetup { required_space }) => {
                        &&& pm_region@ == old(pm_region)@.flush()
                        &&& pm_region@.len() < required_space
                    },
                    _ => false
                }
        {
            let ghost original_pm_region = pm_region@;

            // We can't write without proving that there are no
            // outstanding writes where we're writing. So just start
            // out by flushing, so it's clear we can write anywhere.
            //
            // Why can't we write without proving there isn't a
            // conflicting outstanding write, you ask? Two reasons:
            //
            // First, to simplify the specification of how persistent
            // memory behaves, in `pmem::pmemspec_t.rs` we don't specify
            // what happens when there are multiple outstanding writes
            // to the same address. Instead, we just forbid that
            // case.
            //
            // Second, even if we did specify what happened in that
            // case, in this function we have no idea what's already
            // been written. If there were outstanding writes and they
            // got reordered after our writes, the resulting state
            // might be invalid. So we need to flush before writing
            // anything anyway.

            pm_region.flush();

            // Get the list of region sizes and make sure they support
            // storing a log. If not, return an appropriate
            // error.

            let region_size = pm_region.get_region_size();
            if region_size < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
                return Err(LogErr::InsufficientSpaceForSetup{
                    required_space: ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                });
            }

            // Compute log capacities so we can return them.

            let log_capacity = region_size - ABSOLUTE_POS_OF_LOG_AREA;

            // Write setup metadata.

            write_setup_metadata(pm_region, region_size, Ghost(log_capacity), log_id);

            proof {
                // Prove various postconditions about how we can
                // crash. Specifically, (1) we can only crash as
                // `AbstractLogState::initialize(log_capacities@)`,
                // (2) if we recover after flushing then we get that
                // state, and (3) that state has no pending appends.

                let state = AbstractLogState::initialize(log_capacity as int);
                assert(state =~= state.drop_pending_appends());
                lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(pm_region@);
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
                    pm_region@);
            }

            Ok(log_capacity)
        }

        // The `start` static method creates an
        // `UntrustedLogImpl` out of a set of persistent memory
        // regions. It's assumed that those regions were initialized
        // with `setup` and then only `UntrustedLogImpl` methods
        // were allowed to mutate them. See `README.md` for more
        // documentation and an example of its use.
        //
        // This method is passed a write-restricted collection of
        // persistent memory regions `wrpm_region`. This restricts
        // how we can write `wrpm_region`. This is moot, though,
        // because we don't ever write to the memory.
        pub exec fn start<PMRegion>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            log_id: u128,
            Tracked(perm): Tracked<&TrustedPermission>,
            Ghost(state): Ghost<AbstractLogState>,
        ) -> (result: Result<Self, LogErr>)
            where
                PMRegion: PersistentMemoryRegion
            requires
                Self::recover(old(wrpm_region)@.flush().committed(), log_id) == Some(state),
                old(wrpm_region).inv(),
                forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s, log_id) == Some(state),
            ensures
                wrpm_region.inv(),
                wrpm_region.constants() == old(wrpm_region).constants(),
                match result {
                    Ok(log_impl) => {
                        &&& log_impl.inv(wrpm_region, log_id)
                        &&& log_impl@ == state
                        &&& can_only_crash_as_state(wrpm_region@, log_id, state.drop_pending_appends())
                    },
                    Err(LogErr::CRCMismatch) => !wrpm_region.constants().impervious_to_corruption,
                    _ => false
                }
        {
            // The invariants demand that there are no outstanding
            // writes to various location. To make sure of this, we
            // flush all memory regions.

            wrpm_region.flush();

            // Out of paranoia, we check to make sure that the number
            // of regions is sensible. Both cases are technically
            // precluded by the assumptions about how `start` is
            // invoked, since it's assumed the user invokes `start` on
            // a properly set-up collection of persistent memory
            // regions. We check for them anyway in case that
            // assumption doesn't hold.

            let pm_region = wrpm_region.get_pm_region_ref();

            // First, we read the corruption-detecting boolean and
            // return an error if that fails.

            let cdb = read_cdb(pm_region)?;

            // Second, we read the log variables to store in `info`.
            // If that fails, we return an error.

            let info = read_log_variables(pm_region, log_id, cdb)?;
            proof {
                // We have to prove that we can only crash as the given abstract
                // state with all pending appends dropped. We prove this with two
                // lemmas. The first says that since we've established certain
                // invariants, we can only crash as `state`. The second says that,
                // because this is a recovered state, it's unaffected by dropping
                // all pending appends.

                lemma_invariants_imply_crash_recover_forall(pm_region@, log_id, cdb, info, state);
                lemma_recovered_state_is_crash_idempotent(wrpm_region@.committed(), log_id);
            }
            Ok(Self{ cdb, info, state: Ghost(state) })
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of the log. It's tentative in
        // that crashes will undo the appends, and reads aren't
        // allowed in the tentative part of the log. See `README.md` for
        // more documentation and examples of its use.
        //
        // This method is passed a write-restricted persistent memory
        // region `wrpm_region`. This restricts how it can write
        // `wrpm_region`. It's only given permission (in `perm`) to
        // write if it can prove that any crash after initiating the
        // write is safe. That is, any such crash must put the memory
        // in a state that recovers as the current abstract state with
        // all pending appends dropped.
        pub exec fn tentatively_append<PMRegion>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            bytes_to_append: &[u8],
            Ghost(log_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<u128, LogErr>)
            where
                PMRegion: PersistentMemoryRegion
            requires
                old(self).inv(&*old(wrpm_region), log_id),
                forall |s| #[trigger] perm.check_permission(s) <==>
                    Self::recover(s, log_id) == Some(old(self)@.drop_pending_appends()),
            ensures
                self.inv(wrpm_region, log_id),
                wrpm_region.constants() == old(wrpm_region).constants(),
                can_only_crash_as_state(wrpm_region@, log_id, self@.drop_pending_appends()),
                match result {
                    Ok(offset) => {
                        let state = old(self)@;
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                    },
                    Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                               ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                               ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
                           }
                    },
                    _ => false
                }
        {
            let info = &self.info;

            // One useful invariant implies that
            // `info.log_plus_pending_length <= info.log_area_len`, so
            // we know we can safely do the following subtraction
            // without underflow.

            let available_space: u64 = info.log_area_len - info.log_plus_pending_length as u64;

            // Check to make sure we have enough available space, and
            // return an error otherwise. There are two ways we might
            // not have available space. The first is that doing the
            // append would overfill the log area. The second (which
            // will probably never happen) is that doing this append
            // and a subsequent commit would make the logical tail
            // exceed u128::MAX.

            let num_bytes: u64 = bytes_to_append.len() as u64;
            if num_bytes > available_space {
                return Err(LogErr::InsufficientSpaceForAppend{ available_space })
            }
            if num_bytes as u128 > u128::MAX - info.log_plus_pending_length as u128 - info.head {
                return Err(LogErr::InsufficientSpaceForAppend{
                    available_space: (u128::MAX - info.log_plus_pending_length as u128 - info.head) as u64
                })
            }

            // Compute the current logical offset of the end of the
            // log, including any earlier pending appends. This is the
            // offset at which we'll be logically appending, and so is
            // the offset we're expected to return. After all, the
            // caller wants to know what virtual log position they
            // need to use to read this data in the future.

            let old_pending_tail: u128 = info.head + info.log_plus_pending_length as u128;

            let ghost state = self.state@;

            // The simple case is that we're being asked to append the
            // empty string. If so, do nothing and return.

            if num_bytes == 0 {
                assert(forall |a: Seq<u8>, b: Seq<u8>| b == Seq::<u8>::empty() ==> a + b == a);
                assert(bytes_to_append@ =~= Seq::<u8>::empty());
                assert(self@ =~= old(self)@.tentatively_append(bytes_to_append@));
                return Ok(old_pending_tail);
            }

            // If the number of bytes in the log plus pending appends
            // is at least as many bytes as are beyond the head in the
            // log area, there's obviously enough room to append all
            // the bytes without wrapping. So just write the bytes
            // there.

            if info.log_plus_pending_length >= info.log_area_len - info.head_log_area_offset {

                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + old_pending_tail % info.log_area_len;`
                //
                // But we can replace the expensive modulo operation above with two subtraction
                // operations as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let write_addr: u64 = ABSOLUTE_POS_OF_LOG_AREA +
                    info.log_plus_pending_length - (info.log_area_len - info.head_log_area_offset);
                assert(write_addr == ABSOLUTE_POS_OF_LOG_AREA +
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int,
                                                           info.log_area_len as int));

                proof {
                    lemma_tentatively_append(wrpm_region@, log_id,
                                             bytes_to_append@, self.cdb, self.info, self.state@);
                }
                wrpm_region.write(write_addr, bytes_to_append, Tracked(perm));
            }
            else {

                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + old_pending_tail % info.log_area_len`
                //
                // But we can replace the expensive modulo operation above with an addition
                // operation as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let write_addr: u64 = ABSOLUTE_POS_OF_LOG_AREA +
                    info.log_plus_pending_length + info.head_log_area_offset;
                assert(write_addr == ABSOLUTE_POS_OF_LOG_AREA +
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int,
                                                           info.log_area_len as int));

                // There's limited space beyond the pending bytes in the log area, so as we write
                // the bytes we may have to wrap around the end of the log area. So we must compute
                // how many bytes we can write without having to wrap:

                let max_len_without_wrapping: u64 =
                    info.log_area_len - info.head_log_area_offset - info.log_plus_pending_length;
                assert(max_len_without_wrapping == info.log_area_len -
                       relative_log_pos_to_log_area_offset(info.log_plus_pending_length as int,
                                                           info.head_log_area_offset as int, info.log_area_len as int));

                if num_bytes <= max_len_without_wrapping {

                    // If there's room for all the bytes we need to write, we just need one write.

                    proof {
                        lemma_tentatively_append(wrpm_region@, log_id, bytes_to_append@, self.cdb,
                                                 self.info, self.state@);
                    }
                    wrpm_region.write(write_addr, bytes_to_append, Tracked(perm));
                }
                else {

                    // If there isn't room for all the bytes we need to write, we need two writes,
                    // one writing the first `max_len_without_wrapping` bytes to address
                    // `write_addr` and the other writing the remaining bytes to the beginning of
                    // the log area (`ABSOLUTE_POS_OF_LOG_AREA`).
                    //
                    // There are a lot of things we have to prove about these writes, like the fact
                    // that they're both permitted by `perm`. We offload those proofs to a lemma in
                    // `append_v.rs` that we invoke here.

                    proof {
                        lemma_tentatively_append_wrapping(wrpm_region@, log_id,
                                                          bytes_to_append@, self.cdb, self.info, self.state@);
                    }
                    wrpm_region.write(write_addr,
                                      slice_subrange(bytes_to_append, 0, max_len_without_wrapping as usize),
                                      Tracked(perm));
                    wrpm_region.write(ABSOLUTE_POS_OF_LOG_AREA,
                                      slice_subrange(bytes_to_append, max_len_without_wrapping as usize,
                                                     bytes_to_append.len()),
                                      Tracked(perm));
                }
            }

            // We now update our `info` field to reflect the new
            // `log_plus_pending_length` value.

            self.info.log_plus_pending_length = (info.log_plus_pending_length + num_bytes) as u64;

            // We update our `state` field to reflect the tentative append.

            self.state = Ghost(self.state@.tentatively_append(bytes_to_append@));

            Ok(old_pending_tail)
        }

        // This local helper method updates the log metadata on
        // persistent memory to be consistent with `self.info` and
        // `self.state`. It does so in the following steps: (1) update
        // the log metadata corresponding to the inactive CDB; (2)
        // flush; (3) swap the CDB in region #0; (4) flush again.
        //
        // The first of these steps only writes to inactive metadata, i.e.,
        // metadata that's ignored during recovery. So even if a crash
        // happens during or immediately after this call, recovery will be
        // unaffected.
        //
        // Before calling this function, the caller should make sure that
        // `self.info` and `self.state` contain the data that the inactive
        // log metadata should reflect. But, since this function has to
        // reason about crashes, it also needs to know things about the
        // *previous* values of `self.info` and `self.state`, since those
        // are the ones that the active log metadata is consistent with
        // and will stay consistent with until we write the new CDB. These
        // previous values are passed as ghost parameters since they're
        // only needed for proving things.
        //
        // The caller of this function is responsible for making sure that
        // the contents of the log area are compatible with both the old
        // and the new `info` and `state`. However, the log area contents
        // only need to be compatible with the new `info` and `state`
        // after the next flush, since we're going to be doing a flush.
        // This weaker requirement allows a performance optimization: the
        // caller doesn't have to flush before calling this function.
        exec fn update_log_metadata<PMRegion>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            Ghost(log_id): Ghost<u128>,
            Ghost(prev_info): Ghost<LogInfo>,
            Ghost(prev_state): Ghost<AbstractLogState>,
            Tracked(perm): Tracked<&TrustedPermission>,
        )
            where
                PMRegion: PersistentMemoryRegion
            requires
                old(wrpm_region).inv(),
                memory_matches_deserialized_cdb(old(wrpm_region)@, old(self).cdb),
                no_outstanding_writes_to_metadata(old(wrpm_region)@),
                metadata_consistent_with_info(old(wrpm_region)@, log_id, old(self).cdb, prev_info),
                info_consistent_with_log_area(old(wrpm_region)@.flush(), old(self).info, old(self).state@),
                info_consistent_with_log_area(old(wrpm_region)@, prev_info, prev_state),
                old(self).info.log_area_len == prev_info.log_area_len,
                forall |s| {
                          ||| Self::recover(s, log_id) == Some(prev_state.drop_pending_appends())
                          ||| Self::recover(s, log_id) == Some(old(self).state@.drop_pending_appends())
                      } ==> #[trigger] perm.check_permission(s),
            ensures
                self.inv(wrpm_region, log_id),
                wrpm_region.constants() == old(wrpm_region).constants(),
                self.state == old(self).state,
        {
            // Set the `unused_metadata_pos` to be the position corresponding to !self.cdb
            // since we're writing in the inactive part of the metadata.

            let unused_metadata_pos = if self.cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
                                      else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE };
            assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));

            ///////////////////////////////////////
            // Update the inactive log metadata.
            ///////////////////////////////////////

            // Encode the log metadata as bytes, and compute the CRC of those bytes

            let info = &self.info;
            let log_metadata = LogMetadata {
                head: info.head,
                _padding: 0,
                log_length: info.log_length
            };
            let log_crc = calculate_crc(&log_metadata);

            let ghost log_metadata_bytes = log_metadata.spec_serialize();
            let ghost log_crc_bytes = log_crc.spec_serialize();

            // Prove that updating the inactive metadata+CRC maintains
            // all invariants that held before. We prove this separately
            // for metadata and CRC because they are updated in two separate
            // writes.

            proof {
                LogMetadata::lemma_auto_serialized_len();
                u64::lemma_auto_serialized_len();

                lemma_updating_inactive_metadata_maintains_invariants(
                    wrpm_region@, log_id, self.cdb, prev_info, prev_state, log_metadata_bytes
                );

                let wrpm_region_new = wrpm_region@.write(unused_metadata_pos as int, log_metadata_bytes);
                lemma_updating_inactive_crc_maintains_invariants(
                    wrpm_region_new, log_id, self.cdb, prev_info, prev_state, log_crc_bytes
                );
            }

            // Use `lemma_invariants_imply_crash_recover_forall` to prove that it's OK to call
            // `write`. (One of the conditions for calling that lemma is that our invariants
            // hold, which we just proved above.)

            let ghost wrpm_region_new = wrpm_region@.write(unused_metadata_pos as int, log_metadata_bytes);
            assert forall |crash_bytes| wrpm_region_new.can_crash_as(crash_bytes)
                       implies #[trigger] perm.check_permission(crash_bytes) by {
                lemma_invariants_imply_crash_recover_forall(wrpm_region_new, log_id, self.cdb, prev_info, prev_state);
            }

            // Write the new metadata to the inactive header (without the CRC)
            wrpm_region.serialize_and_write(unused_metadata_pos, &log_metadata, Tracked(perm));

            // Now prove that the CRC is safe to update as well, and write it.

            let ghost wrpm_region_new = wrpm_region@.write(
                unused_metadata_pos + LENGTH_OF_LOG_METADATA, log_crc_bytes
            );
            assert forall |crash_bytes| wrpm_region_new.can_crash_as(crash_bytes)
                       implies #[trigger] perm.check_permission(crash_bytes) by {
                lemma_invariants_imply_crash_recover_forall(
                    wrpm_region_new, log_id, self.cdb, prev_info, prev_state);
            }

            wrpm_region.serialize_and_write(unused_metadata_pos + LENGTH_OF_LOG_METADATA, &log_crc, Tracked(perm));

            // Prove that after the flush, the log metadata corresponding to the unused CDB will
            // be reflected in memory.

            let ghost flushed = wrpm_region_new.flush();
            assert (metadata_consistent_with_info(flushed, log_id, !self.cdb, self.info)) by {
                LogMetadata::lemma_auto_serialize_deserialize();
                u64::lemma_auto_serialize_deserialize();

                let mem1 = wrpm_region@.committed();
                let mem2 = flushed.committed();
                lemma_establish_extract_bytes_equivalence(mem1, mem2);
                lemma_write_reflected_after_flush_committed(wrpm_region@, unused_metadata_pos as int,
                                                            log_metadata_bytes + log_crc_bytes);
                assert(extract_log_metadata(mem2, !self.cdb) =~= log_metadata_bytes);
                assert(extract_log_crc(mem2, !self.cdb) =~= log_crc_bytes);
                assert(deserialize_log_metadata(mem2, !self.cdb) == log_metadata);
                assert(deserialize_log_crc(mem2, !self.cdb) == log_crc);
            }

            // We've updated the inactive log metadata now, so it's a good time to
            // mention some relevant facts about the consequent state.
        
            assert(wrpm_region.inv());
            assert(wrpm_region.constants() == old(wrpm_region).constants());
            assert(unused_metadata_pos == get_log_metadata_pos(!self.cdb));
            assert(memory_matches_deserialized_cdb(wrpm_region@, self.cdb));
            assert(metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, prev_info));
            assert(info_consistent_with_log_area(wrpm_region@, prev_info, prev_state));
            assert(info_consistent_with_log_area(wrpm_region@.flush(), self.info, self.state@));
            assert(forall |s| Self::recover(s, log_id) == Some(prev_state.drop_pending_appends()) ==>
                       #[trigger] perm.check_permission(s));
            assert(self.info.log_area_len == prev_info.log_area_len);
            assert(metadata_consistent_with_info(wrpm_region@.flush(), log_id, !self.cdb, self.info));

            // Prove that after the flush we're about to do, all our
            // invariants will continue to hold (using the still-unchanged
            // CDB and the old metadata, infos, and state).

            proof {
                lemma_flushing_metadata_maintains_invariants(wrpm_region@, log_id, self.cdb, prev_info, prev_state);
            }

            // Next, flush all outstanding writes to memory. This is
            // necessary so that those writes are ordered before the update
            // to the CDB.
            wrpm_region.flush();

            // Next, compute the new encoded CDB to write.

            let new_cdb = if self.cdb { CDB_FALSE } else { CDB_TRUE };
            let ghost new_cdb_bytes = new_cdb.spec_serialize();

            // Show that after writing and flushing, the CDB will be !self.cdb

            let ghost pm_region_after_write = wrpm_region@.write(ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes);
            let ghost flushed_mem_after_write = pm_region_after_write.flush();
            assert(memory_matches_deserialized_cdb(flushed_mem_after_write, !self.cdb)) by {
                u64::lemma_auto_serialize_deserialize();
                u64::lemma_auto_serialized_len();
                let flushed_region = pm_region_after_write.flush();
                lemma_write_reflected_after_flush_committed(wrpm_region@, ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes);
                assert(deserialize_log_cdb(flushed_region.committed()) == new_cdb);
            }

            // Show that after writing and flushing, our invariants will
            // hold for each log if we flip `self.cdb`.

            let ghost pm_region_after_flush = pm_region_after_write.flush();
            assert ({
                &&& metadata_consistent_with_info(pm_region_after_flush, log_id, !self.cdb, self.info)
                &&& info_consistent_with_log_area(pm_region_after_flush, self.info, self.state@)
            }) by {
                u64::lemma_auto_serialize_deserialize();
                u64::lemma_auto_serialized_len();

                lemma_establish_extract_bytes_equivalence(wrpm_region@.committed(),
                                                          pm_region_after_flush.committed());

                lemma_metadata_consistent_with_info_after_cdb_update(
                    wrpm_region@,
                    pm_region_after_flush,
                    log_id,
                    new_cdb_bytes,
                    !self.cdb,
                    self.info
                );
            }
            assert(memory_matches_deserialized_cdb(pm_region_after_flush, !self.cdb));
            // assert(memory_matches_cdb(pm_region_after_flush, !self.cdb));

            // Show that if we crash after the write and flush, we recover
            // to an abstract state corresponding to `self.state@` after
            // dropping pending appends.

            proof {
                lemma_invariants_imply_crash_recover_forall(pm_region_after_flush, log_id,
                                                            !self.cdb, self.info, self.state@);
            }

            // Show that if we crash after initiating the write of the CDB,
            // we'll recover to a permissible state. There are two cases:
            //
            // If we crash without any updating, then we'll recover to
            // state `prev_state.drop_pending_appends()` with the current
            // CDB.
            //
            // If we crash after writing, then we'll recover to state
            // `self.state@.drop_pending_appends()` with the flipped CDB.
            //
            // Because we're only writing within the persistence
            // granularity of the persistent memory, a crash in the middle
            // will either leave the persistent memory in the pre-state or
            // the post-state.
            //
            // This means we're allowed to do the write because if we
            // crash, we'll either be in state wrpm_region@.committed() or
            // pm_region_after_write.flush().committed(). In the former
            // case, we'll be in state `prev_state.drop_pending_appends()`
            // and in the latter case, as shown above, we'll be in state
            // `self.state@.drop_pending_appends()`.

            assert forall |crash_bytes| pm_region_after_write.can_crash_as(crash_bytes) implies
                       #[trigger] perm.check_permission(crash_bytes) by {
                lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_id,
                                                            self.cdb, prev_info, prev_state);
                u64::lemma_auto_serialized_len();
                lemma_single_write_crash_effect_on_pm_region_view(wrpm_region@, ABSOLUTE_POS_OF_LOG_CDB as int,
                                                                  new_cdb_bytes);
            }

            // Finally, update the CDB, then flush, then flip `self.cdb`.
            // There's no need to flip `self.cdb` atomically with the write
            // since the flip of `self.cdb` is happening in local
            // non-persistent memory so if we crash it'll be lost anyway.
            // wrpm_region.write(0, ABSOLUTE_POS_OF_LOG_CDB, new_cdb.as_slice(), Tracked(perm));
            wrpm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_CDB, &new_cdb, Tracked(perm));
            wrpm_region.flush();
            self.cdb = !self.cdb;
        }

        // The `commit` method commits all tentative appends that have been
        // performed since the last one. See `README.md` for more
        // documentation and examples of its use.
        //
        // This method is passed a write-restricted persistent memory
        // region `wrpm_region`. This restricts how it can write
        // `wrpm_region`. It's only given permission (in `perm`) to
        // write if it can prove that any crash after initiating the
        // write is safe. That is, any such crash must put the memory
        // in a state that recovers as either (1) the current abstract
        // state with all pending appends dropped, or (2) the abstract
        // state after all pending appends are committed.
        pub exec fn commit<PMRegion>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            Ghost(log_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<(), LogErr>)
            where
                PMRegion: PersistentMemoryRegion
            requires
                old(self).inv(&*old(wrpm_region), log_id),
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| Self::recover(s, log_id) == Some(old(self)@.drop_pending_appends())
                    ||| Self::recover(s, log_id) == Some(old(self)@.commit().drop_pending_appends())
                },
            ensures
                self.inv(wrpm_region, log_id),
                wrpm_region.constants() == old(wrpm_region).constants(),
                can_only_crash_as_state(wrpm_region@, log_id, self@.drop_pending_appends()),
                result is Ok,
                self@ == old(self)@.commit(),
        {
            let ghost prev_info = self.info;
            let ghost prev_state = self.state@;

            self.state = Ghost(self.state@.commit());

            self.info.log_length = self.info.log_plus_pending_length;

            assert(memory_matches_deserialized_cdb(wrpm_region@, self.cdb));
            assert(metadata_consistent_with_info(wrpm_region@, log_id, self.cdb, prev_info));
            assert(info_consistent_with_log_area(wrpm_region@, prev_info, prev_state));
            assert(self.state@ == prev_state.commit());
            assert(info_consistent_with_log_area(wrpm_region@.flush(), self.info, self.state@));

            // Update the inactive metadata on all regions and flush, then
            // swap the CDB to its opposite.

            self.update_log_metadata(wrpm_region, Ghost(log_id), Ghost(prev_info),
                                     Ghost(prev_state), Tracked(perm));

            Ok(())
        }

        // The `advance_head` method advances the head of the log,
        // thereby making more space for appending but making log
        // entries before the new head unavailable for reading. Upon
        // return from this method, the head advancement is durable,
        // i.e., it will survive crashes. See `README.md` for more
        // documentation and examples of its use.
        //
        // This method is passed a write-restricted persistent memory
        // region `wrpm_region`. This restricts how it can write
        // `wrpm_region`. It's only given permission (in `perm`) to
        // write if it can prove that any crash after initiating the
        // write is safe. That is, any such crash must put the memory
        // in a state that recovers as either (1) the current abstract
        // state with all pending appends dropped, or (2) the state
        // after advancing the head and then dropping all pending
        // appends.
        pub exec fn advance_head<PMRegion>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedPermission, PMRegion>,
            new_head: u128,
            Ghost(log_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedPermission>,
        ) -> (result: Result<(), LogErr>)
            where
                PMRegion: PersistentMemoryRegion
            requires
                old(self).inv(&*old(wrpm_region), log_id),
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| Self::recover(s, log_id) == Some(old(self)@.drop_pending_appends())
                    ||| Self::recover(s, log_id) ==
                        Some(old(self)@.advance_head(new_head as int).drop_pending_appends())
                },
            ensures
                self.inv(wrpm_region, log_id),
                wrpm_region.constants() == old(wrpm_region).constants(),
                can_only_crash_as_state(wrpm_region@, log_id, self@.drop_pending_appends()),
                match result {
                    Ok(()) => {
                        &&& old(self)@.head <= new_head <= old(self)@.head + old(self)@.log.len()
                        &&& self@ == old(self)@.advance_head(new_head as int)
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.head
                        &&& new_head < head
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.head + self@.log.len()
                        &&& new_head > tail
                    },
                    _ => false
                }
        {
            // Even if we return an error code, we still have to prove that
            // upon return the states we can crash into recover into valid
            // abstract states.

            proof {
                lemma_invariants_imply_crash_recover_forall(wrpm_region@, log_id, self.cdb,
                                                            self.info, self.state@);
            }

            // Handle error cases due to improper parameters passed to the
            // function.
            if new_head < self.info.head {
                return Err(LogErr::CantAdvanceHeadPositionBeforeHead{ head: self.info.head })
            }
            if new_head - self.info.head > self.info.log_length as u128 {
                return Err(LogErr::CantAdvanceHeadPositionBeyondTail{
                    tail: self.info.head + self.info.log_length as u128
                })
            }

            // To compute the new head mod n (where n is the log area
            // length), take the old head mod n, add the amount by
            // which the head is advancing, then subtract n if
            // necessary.

            let amount_of_advancement: u64 = (new_head - self.info.head) as u64;
            let new_head_log_area_offset =
                if amount_of_advancement < self.info.log_area_len - self.info.head_log_area_offset {
                    amount_of_advancement + self.info.head_log_area_offset
                }
                else {
                    // To compute `self.info.head_log_area_offset` [the old
                    // head] plus `amount_of_advancement` [the amount
                    // by which the head is advancing] minus
                    // `self.info.log_area_len` [the log area length], we
                    // do it in the following order that guarantees no
                    // overflow/underflow.
                    amount_of_advancement - (self.info.log_area_len - self.info.head_log_area_offset)
                };

            assert(new_head_log_area_offset == new_head as int % self.info.log_area_len as int) by {
                // Here's a mathematical proof that doing the above
                // calculation of `new_head_log_area_offset` achieves the
                // desired computation of `new_head % log_area_len`.

                let n = self.info.log_area_len as int;
                let advancement = amount_of_advancement as int;
                let head = self.info.head as int;
                let head_mod_n = self.info.head_log_area_offset as int;
                let supposed_new_head_mod_n = new_head_log_area_offset as int;

                // First, observe that `advancement` plus `head` is
                // congruent modulo n to `advancement` plus `head` % n.

                assert((advancement + head) % n == (advancement + head_mod_n) % n) by {
                    assert(head == n * (head / n) + head % n) by {
                        lemma_fundamental_div_mod(head, n);
                    }
                    assert((n * (head / n) + (advancement + head_mod_n)) % n == (advancement + head_mod_n) % n) by {
                        lemma_mod_multiples_vanish(head / n, advancement + head_mod_n, n);
                    }
                }

                // Next, observe that `advancement` + `head` % n is
                // congruent modulo n to itself minus n. This is
                // relevant because there are two cases for computing
                // `new_head_mod_log_area_offset`. In one case, it's
                // computed as `advancement` + `head` % n. In the
                // other case, it's that quantity minus n.

                assert((advancement + head % n) % n == (advancement + head_mod_n - n) % n) by {
                    lemma_mod_sub_multiples_vanish(advancement + head_mod_n, n);
                }

                // So we know that in either case, `new_head` % n ==
                // `new_head_mod_log_area_offset` % n.

                assert(new_head as int % n == supposed_new_head_mod_n % n);

                // But what we want to prove is that `new_head` % n ==
                // `new_head_mod_log_area_offset`. So we need to show
                // that `new_head_mod_log_area_offset` % n ==
                // `new_head_mod_log_area_offset`.  We can deduce this
                // from the fact that 0 <= `new_head_mod_log_area_offset`
                // < n.

                assert(supposed_new_head_mod_n % n == supposed_new_head_mod_n) by {
                    lemma_small_mod(supposed_new_head_mod_n as nat, n as nat);
                }
            }

            // Update `self.self.info` to reflect the change to the head
            // position. This necessitates updating all the fields
            // except the log area length.

            let ghost prev_info = self.info;
            self.info.head = new_head;
            self.info.head_log_area_offset = new_head_log_area_offset;
            self.info.log_length = self.info.log_length - amount_of_advancement;
            self.info.log_plus_pending_length = self.info.log_plus_pending_length - amount_of_advancement;

            // Update the abstract `self.state` to reflect the head update.

            let ghost prev_state = self.state@;
            self.state = Ghost(self.state@.advance_head(new_head as int));

            // To prove that the log area for log number `which_log` is
            // compatible with the new `self.infos` and `self.state`, we
            // need to reason about how addresses in the log area
            // correspond to relative log positions. That's because the
            // invariants we know about the log area talk about log
            // positions relative to the old head, but we want to know
            // things about log positions relative to the new head. What
            // connects those together is that they both talk about the
            // same addresses in the log area.

            assert (info_consistent_with_log_area(wrpm_region@.flush(), self.info, self.state@)) by {
                lemma_addresses_in_log_area_correspond_to_relative_log_positions(wrpm_region@, prev_info);
            }

            // Update the inactive metadata on all regions and flush, then
            // swap the CDB to its opposite. We have to update the metadata
            // on all regions, even though we're only advancing the head on
            // one, for the following reason. The only way available to us
            // to update the active metadata is to flip the CDB, but this
            // flips which metadata is active on *all* regions. So we have
            // to update the inactive metadata on all regions.

            self.update_log_metadata(wrpm_region, Ghost(log_id), Ghost(prev_info), Ghost(prev_state),
                                     Tracked(perm));

            Ok(())
        }

        // This local helper method proves that we can read a portion of
        // the abstract log by reading a continuous range of the log area.
        // It requires that the position being read from is correct, and
        // that the read is short enough to not require wrapping around the
        // end of the log area.
        proof fn lemma_read_of_continuous_range(
            &self,
            pm_region_view: PersistentMemoryRegionView,
            log_id: u128,
            pos: int,
            len: int,
            addr: int,
        )
            requires
                len > 0,
                metadata_consistent_with_info(pm_region_view, log_id, self.cdb, self.info),
                info_consistent_with_log_area(pm_region_view, self.info, self.state@),
                ({
                    let info = self.info;
                    let max_len_without_wrapping = info.log_area_len -
                        relative_log_pos_to_log_area_offset(pos - info.head,
                                                            info.head_log_area_offset as int,
                                                            info.log_area_len as int);
                    &&& pos >= info.head
                    &&& pos + len <= info.head + info.log_length
                    &&& len <= max_len_without_wrapping
                    &&& addr == ABSOLUTE_POS_OF_LOG_AREA +
                           relative_log_pos_to_log_area_offset(pos - info.head as int,
                                                               info.head_log_area_offset as int,
                                                               info.log_area_len as int)
                })
            ensures
                ({
                    let log = self@;
                    &&& pm_region_view.no_outstanding_writes_in_range(addr, addr + len)
                    &&& pm_region_view.committed().subrange(addr, addr + len)
                           == log.log.subrange(pos - log.head, pos + len - log.head)
                })
        {
            let info = self.info;
            let s = self.state@;

            // The key to the proof is that we need to reason about how
            // addresses in the log area correspond to relative log
            // positions. This is because the invariant talks about
            // relative log positions but this lemma is proving things
            // about addresses in the log area.

            lemma_addresses_in_log_area_correspond_to_relative_log_positions(pm_region_view, info);
            assert(pm_region_view.committed().subrange(addr, addr + len) =~=
                   s.log.subrange(pos - s.head, pos + len - s.head));
        }

        // The `read` method reads part of the log, returning a vector
        // containing the read bytes. It doesn't guarantee that those
        // bytes aren't corrupted by persistent memory corruption. See
        // `README.md` for more documentation and examples of its use.
        pub exec fn read<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            pos: u128,
            len: u64,
            Ghost(log_id): Ghost<u128>,
        ) -> (result: Result<Vec<u8>, LogErr>)
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
            requires
                self.inv(wrpm_region, log_id),
                pos + len <= u128::MAX
            ensures
                ({
                    let log = self@;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(pos as int, len as int);
                            &&& pos >= log.head
                            &&& pos + len <= log.head + log.log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                              wrpm_region.constants().impervious_to_corruption)
                        },
                        Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < log.head
                            &&& head_pos == log.head
                        },
                        Err(LogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > log.head + log.log.len()
                            &&& tail == log.head + log.log.len()
                        },
                        _ => false
                    }
                })
        {
            // Handle error cases due to improper parameters passed to the
            // function.

            let info = &self.info;
            if pos < info.head {
                return Err(LogErr::CantReadBeforeHead{ head: info.head })
            }
            if len > info.log_length { // We have to do this check first to avoid underflow in the next comparison
                return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }
            if pos - info.head > (info.log_length - len) as u128 { // we know `info.log_length - len` can't underflow
                return Err(LogErr::CantReadPastTail{ tail: info.head + info.log_length as u128 })
            }

            let ghost s = self.state@;
            let ghost true_bytes = s.log.subrange(pos - s.head, pos + len - s.head);

            if len == 0 {
                // Case 0: The trivial case where we're being asked to read zero bytes.

                assert (true_bytes =~= Seq::<u8>::empty());
                assert (maybe_corrupted(Seq::<u8>::empty(), true_bytes, Seq::<int>::empty()));
                return Ok(Vec::<u8>::new());
            }

            let pm_region = wrpm_region.get_pm_region_ref();

            let log_area_len: u64 = info.log_area_len;
            let relative_pos: u64 = (pos - info.head) as u64;
            if relative_pos >= log_area_len - info.head_log_area_offset {

                // Case 1: The position we're being asked to read appears
                // in the log area before the log head. So the read doesn't
                // need to wrap.
                //
                // We could compute the address to write to with:
                //
                // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
                //
                // But we can replace the expensive modulo operation above with two subtraction
                // operations as follows. This is somewhat subtle, but we have verification backing
                // us up and proving this optimization correct.

                let addr = ABSOLUTE_POS_OF_LOG_AREA + relative_pos - (info.log_area_len - info.head_log_area_offset);
                proof { self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                            len as int, addr as int); }
                return Ok(pm_region.read(addr, len));
            }

            // The log area wraps past the point we're reading from, so we
            // need to compute the maximum length we can read without
            // wrapping to be able to figure out whether we need to wrap.

            let max_len_without_wrapping: u64 = log_area_len - info.head_log_area_offset - relative_pos;
            assert(max_len_without_wrapping == info.log_area_len -
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int, info.log_area_len as int));

            // Whether we need to wrap or not, we know the address where
            // our read should start, so we can compute that and put it in
            // `addr`.
            //
            // We could compute the address to write to with:
            //
            // `write_addr = ABSOLUTE_POS_OF_LOG_AREA + pos % info.log_area_len;`
            //
            // But we can replace the expensive modulo operation above with
            // one addition operation as follows. This is somewhat subtle,
            // but we have verification backing us up and proving this
            // optimization correct.

            let addr: u64 = ABSOLUTE_POS_OF_LOG_AREA + relative_pos + info.head_log_area_offset;
            assert(addr == ABSOLUTE_POS_OF_LOG_AREA +
                   relative_log_pos_to_log_area_offset(pos - info.head,
                                                       info.head_log_area_offset as int,
                                                       info.log_area_len as int));

            if len <= max_len_without_wrapping {

                // Case 2: We're reading few enough bytes that we don't have to wrap.

                proof { self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                            len as int, addr as int); }
                return Ok(pm_region.read(addr, len));
            }

            // Case 3: We're reading enough bytes that we have to wrap.
            // That necessitates doing two contiguous reads, one from the
            // end of the log area and one from the beginning, and
            // concatenating the results.

            proof {
                self.lemma_read_of_continuous_range(pm_region@, log_id, pos as int,
                                                    max_len_without_wrapping as int, addr as int);
            }

            let mut part1 = pm_region.read(addr, max_len_without_wrapping);

            proof {
                self.lemma_read_of_continuous_range(pm_region@, log_id,
                                                    pos + max_len_without_wrapping,
                                                    len - max_len_without_wrapping,
                                                    ABSOLUTE_POS_OF_LOG_AREA as int);
            }

            let mut part2 = pm_region.read(ABSOLUTE_POS_OF_LOG_AREA,
                                            len - max_len_without_wrapping);

            // Now, prove that concatenating them produces the correct
            // bytes to return. The subtle thing in this argument is that
            // the bytes are only correct modulo corruption. And the
            // "correct modulo corruption" specification function talks
            // about the concrete addresses the bytes were read from and
            // demands that those addresses all be distinct.

            proof {
                let true_part1 = s.log.subrange(pos - s.head, pos + max_len_without_wrapping - s.head);
                let true_part2 = s.log.subrange(pos + max_len_without_wrapping - s.head, pos + len - s.head);
                let addrs1 = Seq::<int>::new(max_len_without_wrapping as nat, |i: int| i + addr);
                let addrs2 = Seq::<int>::new((len - max_len_without_wrapping) as nat,
                                           |i: int| i + ABSOLUTE_POS_OF_LOG_AREA);
                assert(true_part1 + true_part2 =~= s.log.subrange(pos - s.head, pos + len - s.head));

                if !pm_region.constants().impervious_to_corruption {
                    assert(maybe_corrupted(part1@ + part2@, true_part1 + true_part2, addrs1 + addrs2));
                    assert(all_elements_unique(addrs1 + addrs2));
                }
            }

            // Append the two byte vectors together and return the result.

            part1.append(&mut part2);
            Ok(part1)
        }

        // The `get_head_tail_and_capacity` method returns the head,
        // tail, and capacity of the log. See `README.md` for more
        // documentation and examples of its use.
        #[allow(unused_variables)]
        pub exec fn get_head_tail_and_capacity<Perm, PMRegion>(
            &self,
            wrpm_region: &WriteRestrictedPersistentMemoryRegion<Perm, PMRegion>,
            Ghost(log_id): Ghost<u128>,
        ) -> (result: Result<(u128, u128, u64), LogErr>)
            where
                Perm: CheckPermission<Seq<u8>>,
                PMRegion: PersistentMemoryRegion
            requires
                self.inv(wrpm_region, log_id)
            ensures
                ({
                    let log = self@;
                    match result {
                        Ok((result_head, result_tail, result_capacity)) => {
                            &&& result_head == log.head
                            &&& result_tail == log.head + log.log.len()
                            &&& result_capacity == log.capacity
                        },
                        _ => false
                    }
                })
        {
            // We cache information in `self.info` that lets us easily
            // compute the return values.

            let info = &self.info;
            Ok((info.head, info.head + info.log_length as u128, info.log_area_len))
        }

    }

}
