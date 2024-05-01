//! This file contains functions for starting to use persistent memory
//! as a multilog. Such starting is done either after setup or after a
//! crash.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::multilog::inv_v::*;
use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::MultiLogErr;
use crate::multilog::multilogimpl_v::LogInfo;
use crate::multilog::multilogspec_t::AbstractMultiLogState;
use crate::pmem::pmemspec_t::{PersistentMemoryRegions, CRC_SIZE};
use crate::pmem::pmemutil_v::{check_cdb, check_crc_deserialized};
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::arithmetic::div_mod::*;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

    // This exported function reads the corruption-detecting boolean
    // and returns it.
    //
    // `pm_regions` -- the persistent-memory regions to read from
    //
    // The result is a `Result<bool, MultiLogErr>` with the following meanings:
    //
    // `Err(MultiLogErr::CRCMismatch)` -- The CDB couldn't be read due
    // to a CRC error.
    //
    // `Ok(b)` -- The CDB could be read and represents the boolean `b`.
    pub fn read_cdb<PMRegions: PersistentMemoryRegions>(pm_regions: &PMRegions) -> (result: Result<bool, MultiLogErr>)
        requires
            pm_regions.inv(),
            pm_regions@.len() > 0,
            recover_cdb(pm_regions@[0].committed()).is_Some(),
            pm_regions@.no_outstanding_writes(),
        ensures
            match result {
                Ok(b) => Some(b) == recover_cdb(pm_regions@[0].committed()),
                // To make sure this code doesn't spuriously generate CRC-mismatch errors,
                // it's obligated to prove that it won't generate such an error when
                // the persistent memory is impervious to corruption.
                Err(MultiLogErr::CRCMismatch) => !pm_regions.constants().impervious_to_corruption,
                _ => false,
            }
    {
        let ghost mem = pm_regions@[0].committed();

        // let log_cdb_bytes = pm_regions.read(0, ABSOLUTE_POS_OF_LOG_CDB, CRC_SIZE);
        let log_cdb = pm_regions.read_and_deserialize::<u64>(0, ABSOLUTE_POS_OF_LOG_CDB);
        let result = check_cdb(&log_cdb, Ghost(mem),
                               Ghost(pm_regions.constants().impervious_to_corruption),
                               Ghost(ABSOLUTE_POS_OF_LOG_CDB));
        match result {
            Some(b) => Ok(b),
            None => Err(MultiLogErr::CRCMismatch)
        }
    }

    // This function reads the log information for a single log from
    // persistent memory.
    //
    // `pm_regions` -- the persistent memory regions to read from
    //
    // `multilog_id` -- the GUID of the multilog
    //
    // `cdb` -- the corruption-detection boolean
    //
    // `num_logs` -- the number of logs in the multilog
    //
    // `which_log` -- which among the multilog's logs to read
    //
    // The result is a `Result<LogInfo, MultiLogErr>` with the following meanings:
    //
    // `Ok(log_info)` -- The information `log_info` has been
    // successfully read.
    //
    // `Err(MultiLogErr::CRCMismatch)` -- The region couldn't be read due
    // to a CRC error when reading data.
    //
    // `Err(MultiLogErr::StartFailedDueToProgramVersionNumberUnsupported)`
    // -- The program version number stored in persistent memory is
    // one that this code doesn't know how to recover from. It was
    // presumably created by a later version of this code.
    //
    // `Err(MultiLogErr::StartFailedDueToMultilogIDMismatch)` -- The
    // multilog ID stored in persistent memory doesn't match the one
    // passed to the `start` routine. So the caller of `start` gave
    // the wrong persistent memory region or the wrong ID.
    //
    // `Err(MultiLogErr::StartFailedDueToRegionSizeMismatch)` -- The
    // region size stored in persistent memory doesn't match the size
    // of the region passed to the `start` routine. So the caller of
    // `start` is likely using a persistent memory region that starts
    // in the right place but ends in the wrong place.
    //
    // `Err(MultiLogErr::StartFailedDueToInvalidMemoryContents)` --
    // The region's contents aren't valid, i.e., they're not
    // recoverable to a valid log. The user must have requested to
    // start using the wrong region of persistent memory.
    fn read_log_variables<PMRegions: PersistentMemoryRegions>(
        pm_regions: &PMRegions,
        multilog_id: u128,
        cdb: bool,
        num_logs: u32,
        which_log: u32,
    ) -> (result: Result<LogInfo, MultiLogErr>)
        requires
            pm_regions.inv(),
            is_valid_log_index(which_log, num_logs),
            num_logs == pm_regions@.len(),
            pm_regions@[which_log as int].no_outstanding_writes(),
        ensures
            ({
                let w = which_log as int;
                let state = recover_abstract_log_from_region_given_cdb(pm_regions@[w].committed(), multilog_id,
                                                                       num_logs as int, w, cdb);
                match result {
                    Ok(info) => state.is_Some() ==> {
                        &&& metadata_consistent_with_info(pm_regions@[w], multilog_id, num_logs, which_log, cdb, info)
                        &&& info_consistent_with_log_area(pm_regions@[w], info, state.unwrap())
                    },
                    Err(MultiLogErr::CRCMismatch) =>
                        state.is_Some() ==> !pm_regions.constants().impervious_to_corruption,
                    _ => state.is_None()
                }
            })
    {
        let ghost mem = pm_regions@[which_log as int].committed();
        let ghost w = which_log as int;
        let ghost state = recover_abstract_log_from_region_given_cdb(pm_regions@[w].committed(), multilog_id,
                                                                     num_logs as int, w, cdb);

        // Check that the region is at least the minimum required size. If
        // not, indicate invalid memory contents.

        let region_size = pm_regions.get_region_size(which_log as usize);
        if region_size < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        // Read the level-1 metadata and its CRC, and check that the
        // CRC matches.

        let global_metadata = pm_regions.read_and_deserialize::<GlobalMetadata>(which_log as usize, ABSOLUTE_POS_OF_GLOBAL_METADATA);
        let global_crc = pm_regions.read_and_deserialize(which_log as usize, ABSOLUTE_POS_OF_GLOBAL_CRC);
        if !check_crc_deserialized(global_metadata, global_crc,
                      Ghost(mem), Ghost(pm_regions.constants().impervious_to_corruption),
                      Ghost(ABSOLUTE_POS_OF_GLOBAL_METADATA), Ghost(LENGTH_OF_GLOBAL_METADATA),
                      Ghost(ABSOLUTE_POS_OF_GLOBAL_CRC)) {
            proof {
                // assert(pm_regions.constants().impervious_to_corruption);
                // assert(!pm_regions.constants().impervious_to_corruption);
            }

            return Err(MultiLogErr::CRCMismatch);
        }

        // Check the level-1 metadata for validity. If it isn't valid,
        // e.g., due to the program GUID not matching, then return an
        // error. Such invalidity can't happen if the persistent
        // memory is recoverable.

        if global_metadata.program_guid != MULTILOG_PROGRAM_GUID {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        if global_metadata.version_number != MULTILOG_PROGRAM_VERSION_NUMBER {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToProgramVersionNumberUnsupported{
                which_log,
                version_number: global_metadata.version_number,
                max_supported: MULTILOG_PROGRAM_VERSION_NUMBER,
            })
        }

        if global_metadata.length_of_region_metadata != LENGTH_OF_REGION_METADATA {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        // Read the level-2 metadata and its CRC, and check that the
        // CRC matches.

        let region_metadata = pm_regions.read_and_deserialize::<RegionMetadata>(which_log as usize, ABSOLUTE_POS_OF_REGION_METADATA);
        let region_crc = pm_regions.read_and_deserialize(which_log as usize, ABSOLUTE_POS_OF_REGION_CRC);
        if !check_crc_deserialized(region_metadata, region_crc,
                      Ghost(mem), Ghost(pm_regions.constants().impervious_to_corruption),
                      Ghost(ABSOLUTE_POS_OF_REGION_METADATA), Ghost(LENGTH_OF_REGION_METADATA),
                      Ghost(ABSOLUTE_POS_OF_REGION_CRC)) {
            return Err(MultiLogErr::CRCMismatch);
        }

        // Check the level-2 metadata for validity. If it isn't valid,
        // e.g., due to the encoded region size not matching the
        // actual region size, then return an error. Such invalidity
        // can't happen if the persistent memory is recoverable.

        if region_metadata.region_size != region_size {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToRegionSizeMismatch{
                which_log,
                region_size_expected: region_size,
                region_size_read: region_metadata.region_size,
            })
        }

        if region_metadata.multilog_id != multilog_id {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToMultilogIDMismatch{
                which_log,
                multilog_id_expected: multilog_id,
                multilog_id_read: region_metadata.multilog_id,
            })
        }

        if region_metadata.num_logs != num_logs {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        if region_metadata.which_log != which_log {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        if region_metadata.log_area_len > region_size {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }
        if region_size - region_metadata.log_area_len < ABSOLUTE_POS_OF_LOG_AREA {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }
        if region_metadata.log_area_len < MIN_LOG_AREA_SIZE {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        // Read the level-3 metadata and its CRC, and check that the
        // CRC matches. The position where to find the level-3
        // metadata depend on the CDB.

        let log_metadata_pos = if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE }
                                  else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE };
        let log_crc_pos = if cdb { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                             else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
        let log_metadata = pm_regions.read_and_deserialize::<LogMetadata>(which_log as usize, log_metadata_pos);
        let log_crc = pm_regions.read_and_deserialize::<u64>(which_log as usize, log_crc_pos);
        if !check_crc_deserialized(log_metadata, log_crc, Ghost(mem), Ghost(pm_regions.constants().impervious_to_corruption),
                                    Ghost(log_metadata_pos), Ghost(LENGTH_OF_LOG_METADATA), Ghost(log_crc_pos)) {
            return Err(MultiLogErr::CRCMismatch);
        }

        // Check the level-3 metadata for validity. If it isn't valid,
        // e.g., due to the log length being greater than the log area
        // length, then return an error. Such invalidity can't happen
        // if the persistent memory is recoverable.

        let head = log_metadata.head;
        let log_length = log_metadata.log_length;
        if log_length > region_metadata.log_area_len {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }
        if log_length as u128 > u128::MAX - head {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(MultiLogErr::StartFailedDueToInvalidMemoryContents{ which_log })
        }

        // Compute the offset into the log area where the head of the
        // log is. This is the u128 `head` mod the u64
        // `log_area_len`. To prove that this will fit in a `u64`, we
        // need to invoke a math lemma saying that the result of a
        // modulo operation is always less than the divisor.

        proof { lemma_mod_bound(head as int, region_metadata.log_area_len as int); }
        let head_log_area_offset: u64 = (head % region_metadata.log_area_len as u128) as u64;

        // Return the log info. This necessitates computing the
        // pending tail position relative to the head, but this is
        // easy: It's the same as the log length. This is because,
        // upon recovery, there are no pending appends beyond the tail
        // of the log.

        Ok(LogInfo{
            log_area_len: region_metadata.log_area_len,
            head,
            head_log_area_offset,
            log_length,
            log_plus_pending_length: log_length
        })
    }

    // This function reads the log information for all logs in a
    // collection of persistent memory regions
    //
    // `pm_regions` -- the persistent memory regions to read from
    //
    // `multilog_id` -- the GUID of the multilog
    //
    // `cdb` -- the corruption-detection boolean
    //
    // `num_regions` -- the number of regions in the collection of
    // persistent memory regions
    //
    // `state` -- the abstract state that this memory is known to be
    // recoverable to
    //
    // The result is a `Result<LogInfo, MultiLogErr>` with the following meanings:
    //
    // `Err(MultiLogErr::CRCMismatch)` -- The region couldn't be read due
    // to a CRC error when reading data.
    //
    // `Ok(log_info)` -- The information `log_info` has been
    // successfully read.
    pub fn read_logs_variables<PMRegions: PersistentMemoryRegions>(
        pm_regions: &PMRegions,
        multilog_id: u128,
        cdb: bool,
        num_regions: u32,
        Ghost(state): Ghost<AbstractMultiLogState>,
    ) -> (result: Result<Vec<LogInfo>, MultiLogErr>)
        requires
            pm_regions.inv(),
            num_regions == pm_regions@.len(),
            num_regions > 0,
            pm_regions@.no_outstanding_writes(),
            memory_matches_deserialized_cdb(pm_regions@, cdb),
            recover_given_cdb(pm_regions@.committed(), multilog_id, cdb) == Some(state),
        ensures
            match result {
                Ok(info) => {
                    &&& each_metadata_consistent_with_info(pm_regions@, multilog_id, num_regions, cdb, info@)
                    &&& each_info_consistent_with_log_area(pm_regions@, num_regions, info@, state)
                },
                Err(MultiLogErr::CRCMismatch) => !pm_regions.constants().impervious_to_corruption,
                _ => false,
            }
    {
        let mut infos = Vec::<LogInfo>::new();
        for which_log in 0..num_regions
            invariant
                pm_regions.inv(),
                which_log == infos.len(),
                forall |j:u32| j < which_log ==> {
                    &&& info_consistent_with_log_area(#[trigger] pm_regions@[j as int], infos[j as int], state[j as int])
                    &&& metadata_consistent_with_info(pm_regions@[j as int], multilog_id, num_regions, j, cdb,
                                                    infos[j as int])
                },
                num_regions == pm_regions@.len(),
                recover_given_cdb(pm_regions@.committed(), multilog_id, cdb) == Some(state),
                pm_regions@.no_outstanding_writes(),
        {
            // Before calling `read_log_variables`, establish that
            // region `which_log` is recoverable. This is useful
            // because the postcondition of `read_log_variables`
            // doesn't let one draw many conclusions unless one knows
            // the region is recoverable.

            let ghost region_state = recover_abstract_log_from_region_given_cdb(
                pm_regions@[which_log as int].committed(), multilog_id, num_regions as int, which_log as int, cdb);
            assert (region_state.is_Some()) by {
                // To trigger the `forall` inside `recover_given_cdb`, we need to set a ghost
                // variable to the `seq_option` value created inside `recover_given_cdb`.
                let ghost seq_option = pm_regions@.committed().map(
                    |idx, c| recover_abstract_log_from_region_given_cdb(c, multilog_id, num_regions as int,
                                                                        idx, cdb));
                // Then, we trigger it by mentioning `seq_option[which_log as int]`.
                assert(region_state == seq_option[which_log as int]);
            }

            let info = read_log_variables(pm_regions, multilog_id, cdb, num_regions, which_log)?;
            infos.push(info);
        }
        Ok(infos)
    }
}
