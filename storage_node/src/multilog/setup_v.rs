//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::MultiLogErr;
use crate::multilog::multilogspec_t::AbstractMultiLogState;
use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    // This exported executable function checks whether there's enough
    // space on persistent memory regions to support a multilog.
    //
    // `region_sizes` -- a vector of sizes, one per region
    // `num_regions` -- the number of regions (equal to the length of the `region_sizes` array)
    //
    // The return value is a `Result<(), MultiLogErr>`, meaning the following:
    //
    // `Ok(())` -- there's enough space on each region
    // `Err(err)` -- there isn't enough space, so the caller should return the error `err`.
    pub fn check_for_required_space(region_sizes: &Vec<u64>, num_regions: u32) -> (result: Result<(), MultiLogErr>)
        requires
            num_regions == region_sizes.len()
        ensures
            ({
                match result {
                    Ok(()) => forall |i| 0 <= i < region_sizes@.len() ==>
                        region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                    Err(MultiLogErr::InsufficientSpaceForSetup{ which_log, required_space }) => {
                        &&& 0 <= which_log < region_sizes@.len()
                        &&& region_sizes[which_log as int] < required_space
                        &&& required_space == ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                    },
                    _ => false,
                }
            })
    {
        // Loop through all the regions, checking for sufficiency of
        // size.

        for which_log in 0..num_regions
            invariant
                num_regions == region_sizes.len(),
                forall |j| 0 <= j < which_log ==> region_sizes[j] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        {
            if region_sizes[which_log as usize] < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
                return Err(MultiLogErr::InsufficientSpaceForSetup{
                    which_log,
                    required_space: ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
                });
            }
        }
        Ok(())
    }

    // This exported function computes the log capacities allowed by the given region sizes.
    pub fn compute_log_capacities(region_sizes: &Vec<u64>) -> (result: Vec<u64>)
        requires
            forall |i: int| 0 <= i < region_sizes.len() ==> region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        ensures
            result.len() == region_sizes.len(),
            forall |i: int| 0 <= i < region_sizes.len() ==>
                #[trigger] result[i] + ABSOLUTE_POS_OF_LOG_AREA == region_sizes[i]
    {
        let mut result = Vec::<u64>::new();
        for which_region in iter: 0..region_sizes.len()
            invariant
                iter.end == region_sizes.len(),
                forall |i: int| 0 <= i < region_sizes.len() ==> region_sizes[i] >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                result.len() == which_region,
                forall |i: int| 0 <= i < which_region ==>
                    #[trigger] result[i] + ABSOLUTE_POS_OF_LOG_AREA == region_sizes[i]
        {
            result.push(region_sizes[which_region] - ABSOLUTE_POS_OF_LOG_AREA);
        }
        result
    }

    // This helper function computes level-1 metadata and returns an
    // encoding of it.
    fn compute_level1_metadata_encoded() -> (result: Vec<u8>)
        ensures
            result@.len() == LENGTH_OF_LEVEL1_METADATA,
            ({
                let level1_metadata = parse_level1_metadata(result@);
                &&& level1_metadata.program_guid == MULTILOG_PROGRAM_GUID
                &&& level1_metadata.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
                &&& level1_metadata.length_of_level2_metadata == LENGTH_OF_LEVEL2_METADATA
            })
    {
        // Initialize an empty vector.
        let mut result = Vec::<u8>::new();

        // Append the little-endian encoding of our program GUID.
        let mut t = u128_to_le_bytes(MULTILOG_PROGRAM_GUID);
        result.append(&mut t);

        // Append the little-endian encoding of our program version number.
        let mut t = u64_to_le_bytes(MULTILOG_PROGRAM_VERSION_NUMBER);
        result.append(&mut t);

        // Append the little-endian encoding of the length of our level-2 metadata.
        let mut t = u64_to_le_bytes(LENGTH_OF_LEVEL2_METADATA);
        result.append(&mut t);

        proof {
            // We want to prove that if we call
            // `parse_level1_metadata` on `result`, we get the desired
            // level-1 metadata. The proof is in two parts.

            // Part 1:
            // Prove that if we extract pieces of `result`, we get the
            // little-endian encodings of the desired level-1
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL1_PROGRAM_GUID as int, 16)
                   =~= spec_u128_to_le_bytes(MULTILOG_PROGRAM_GUID));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL1_VERSION_NUMBER as int, 8)
                   =~= spec_u64_to_le_bytes(MULTILOG_PROGRAM_VERSION_NUMBER));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL1_LENGTH_OF_LEVEL2_METADATA as int, 8)
                   =~= spec_u64_to_le_bytes(LENGTH_OF_LEVEL2_METADATA));

            // Part 2:
            // Prove that if we parse the various little-endian-encoded values,
            // we get the values that were encoded. This involves invoking the
            // lemmas that say the `to` and `from` functions are inverses.

            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        result
    }

    // This helper function computes level-2 metadata for a region and
    // returns an encoding of it. Because level-2 metadata encodes
    // various information about this region and the multilog it's
    // part of, the function needs some parameters:
    //
    // `region_size`: how big this region is
    // `multilog_id`: the GUID of the multilog it's being used for
    // `num_logs`: the number of logs in the multilog
    // `which_log`: which among those logs this region is for
    fn compute_level2_metadata_encoded(
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
    ) -> (result: Vec<u8>)
        requires
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            which_log < num_logs,
        ensures
            result@.len() == LENGTH_OF_LEVEL2_METADATA,
            ({
                let level2_metadata = parse_level2_metadata(result@);
                &&& level2_metadata.region_size == region_size
                &&& level2_metadata.multilog_id == multilog_id
                &&& level2_metadata.num_logs == num_logs
                &&& level2_metadata.which_log == which_log
                &&& level2_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
            })
    {
        // Initialize an empty vector.
        let mut result = Vec::<u8>::new();

        // Append the little-endian encoding of this region's size.
        let mut t = u64_to_le_bytes(region_size);
        result.append(&mut t);

        // Append the little-endian encoding of the multilog ID.
        let mut t = u128_to_le_bytes(multilog_id);
        result.append(&mut t);

        // Append the little-endian encoding of the number of logs.
        let mut t = u32_to_le_bytes(num_logs);
        result.append(&mut t);

        // Append the little-endian encoding of which log this is.
        let mut t = u32_to_le_bytes(which_log);
        result.append(&mut t);

        // Append the little-endian encoding of this log's log area length.
        let log_area_len: u64 = (region_size - ABSOLUTE_POS_OF_LOG_AREA) as u64;
        let mut t = u64_to_le_bytes(log_area_len);
        result.append(&mut t);

        proof {
            // We want to prove that if we call `parse_level2_metadata` on `result`,
            // we get the desired level-2 metadata. The proof is in two parts.

            // Part 1:
            // Prove that if we extract pieces of `result`, we get the
            // little-endian encodings of the desired level-2
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL2_REGION_SIZE as int, 8)
                   =~= spec_u64_to_le_bytes(region_size));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL2_MULTILOG_ID as int, 16)
                   =~= spec_u128_to_le_bytes(multilog_id));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL2_NUM_LOGS as int, 4)
                   =~= spec_u32_to_le_bytes(num_logs));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL2_WHICH_LOG as int, 4)
                   =~= spec_u32_to_le_bytes(which_log));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL2_LENGTH_OF_LOG_AREA as int, 8)
                   =~= spec_u64_to_le_bytes(log_area_len));

            // Part 2:
            // Prove that if we parse the various little-endian-encoded values,
            // we get the values that were encoded. This involves invoking the
            // lemmas that say the `to` and `from` functions are inverses.

            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        result
    }

    // This helper function computes level-3 metadata for a region and
    // returns an encoding of it. Because level-3 metadata encodes
    // various information about this region, the function needs some
    // parameters:
    //
    // `head`: the logical position of the log's head
    // `log_length`: the number of log bytes beyond the head
    pub fn compute_level3_metadata_encoded(
        head: u128,
        log_length: u64
    ) -> (result: Vec<u8>)
        ensures
            result@.len() == LENGTH_OF_LEVEL3_METADATA,
            ({
                let level3_metadata = parse_level3_metadata(result@);
                &&& level3_metadata.head == head
                &&& level3_metadata.log_length == log_length
            })
    {
        // Initialize an empty vector.
        let mut result = Vec::<u8>::new();

        // Append the little-endian encoding of the head.
        let mut t = u128_to_le_bytes(head);
        result.append(&mut t);

        // Append the little-endian encoding of the log's length.
        let mut t = u64_to_le_bytes(log_length);
        result.append(&mut t);

        proof {
            // We want to prove that if we call `parse_level3_metadata` on `result`,
            // we get the desired level-3 metadata. The proof is in two parts.

            // Part 1:
            // Prove that if we extract pieces of `result`, we get the
            // little-endian encodings of the desired level-3
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL3_HEAD as int, 16)
                   =~= spec_u128_to_le_bytes(head));
            assert(extract_bytes(result@, RELATIVE_POS_OF_LEVEL3_LOG_LENGTH as int, 8)
                   =~= spec_u64_to_le_bytes(log_length));

            // Part 2:
            // Prove that if we parse the various little-endian-encoded values,
            // we get the values that were encoded. This involves invoking the
            // lemmas that say the `to` and `from` functions are inverses.

            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        result
    }

    // This function evaluates whether memory was correctly set up on
    // a single region. It's a helpful specification function for use
    // in later functions in this file.
    //
    // Because answering this question depends on knowing various
    // metadata about this region and the multilog it's part of, the
    // function needs various input parameters for that. Its
    // parameters are:
    //
    // `mem` -- the contents of memory for this region
    // `region_size` -- how big this region is
    // `multilog_id` -- the GUID of the multilog it's being used for
    // `num_logs` -- the number of logs in the multilog
    // `which_log` -- which among those logs this region is for
    spec fn memory_correctly_set_up_on_single_region(
        mem: Seq<u8>,
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
    ) -> bool
    {
        let level1_metadata_bytes = extract_level1_metadata(mem);
        let level1_crc = extract_level1_crc(mem);
        let level1_metadata = parse_level1_metadata(level1_metadata_bytes);
        let level2_metadata_bytes = extract_level2_metadata(mem);
        let level2_crc = extract_level2_crc(mem);
        let level2_metadata = parse_level2_metadata(level2_metadata_bytes);
        let level3_cdb = extract_and_parse_level3_cdb(mem);
        let level3_metadata_bytes = extract_level3_metadata(mem, false);
        let level3_crc = extract_level3_crc(mem, false);
        let level3_metadata = parse_level3_metadata(level3_metadata_bytes);
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        &&& mem.len() == region_size
        &&& level1_crc == spec_crc_bytes(level1_metadata_bytes)
        &&& level2_crc == spec_crc_bytes(level2_metadata_bytes)
        &&& level3_crc == spec_crc_bytes(level3_metadata_bytes)
        &&& level1_metadata.program_guid == MULTILOG_PROGRAM_GUID
        &&& level1_metadata.version_number == MULTILOG_PROGRAM_VERSION_NUMBER
        &&& level1_metadata.length_of_level2_metadata == LENGTH_OF_LEVEL2_METADATA
        &&& level2_metadata.region_size == region_size
        &&& level2_metadata.multilog_id == multilog_id
        &&& level2_metadata.num_logs == num_logs
        &&& level2_metadata.which_log == which_log
        &&& level2_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
        &&& level3_cdb == Some(false)
        &&& level3_metadata.head == 0
        &&& level3_metadata.log_length == 0
    }

    // This executable function sets up a single region for use in a
    // multilog. To do so, it needs various metadata about this region
    // and the multilog it's part of, so it needs some parameters:
    //
    // `region_size`: how big this region is
    // `multilog_id`: the GUID of the multilog it's being used for
    // `num_logs`: the number of logs in the multilog
    // `which_log`: which among those logs this region is for
    //
    // It also needs the parameter `pm_regions` that gives the
    // persistent memory regions for us to write to. It'll only write
    // to region number `which_log`.
    //
    // The main postcondition is:
    //
    // `memory_correctly_set_up_on_single_region(pm_regions@[which_log as int].flush().committed(),
    //                                           region_size, multilog_id, num_logs, which_log)`
    //
    // This means that, after the next flush, the memory in this
    // region will have been set up correctly. (This function doesn't
    // do the flush, for efficiency. That way we only need one flush
    // operation to flush all regions.)
    fn write_setup_metadata_to_single_region<PMRegions: PersistentMemoryRegions>(
        pm_regions: &mut PMRegions,
        region_size: u64,
        multilog_id: u128,
        num_logs: u32,
        which_log: u32,
    )
        requires
            old(pm_regions).inv(),
            num_logs == old(pm_regions)@.len(),
            which_log < num_logs,
            old(pm_regions)@[which_log as int].no_outstanding_writes(),
            old(pm_regions)@[which_log as int].len() == region_size,
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
        ensures
            pm_regions.inv(),
            pm_regions.constants() == old(pm_regions).constants(),
            pm_regions@.len() == old(pm_regions)@.len(),
            forall |i: int| 0 <= i < pm_regions@.len() && i != which_log ==> pm_regions@[i] == old(pm_regions)@[i],
            memory_correctly_set_up_on_single_region(
                pm_regions@[which_log as int].flush().committed(), // it'll be correct after the next flush
                region_size, multilog_id, num_logs, which_log),
    {
        // Initialize an empty vector.
        let mut bytes_to_write = Vec::<u8>::new();

        // Compute an encoding of the level-1 metadata, and append that to the vector.
        // Also, compute a CRC of that encoding and append that.
        let mut t = compute_level1_metadata_encoded();
        let mut c = bytes_crc(t.as_slice());
        let ghost level1_metadata = t@;
        let ghost level1_crc = c@;
        bytes_to_write.append(&mut t);
        bytes_to_write.append(&mut c);

        // Compute an encoding of the level-2 metadata, and append that to the vector.
        // Also, compute a CRC of that encoding and append that.
        let mut t = compute_level2_metadata_encoded(region_size, multilog_id, num_logs, which_log);
        let mut c = bytes_crc(t.as_slice());
        let ghost level2_metadata = t@;
        let ghost level2_crc = c@;
        bytes_to_write.append(&mut t);
        bytes_to_write.append(&mut c);

        // Append the corruption-detecting encoding of the corruption detecting boolean value `false`.
        let mut t = u64_to_le_bytes(CDB_FALSE);
        bytes_to_write.append(&mut t);

        // Compute an encoding of the level-3 metadata, and append that to the vector.
        // Also, compute a CRC of that encoding and append that.
        let mut t = compute_level3_metadata_encoded(0, 0);
        let mut c = bytes_crc(t.as_slice());
        let ghost level3_metadata = t@;
        let ghost level3_crc = c@;
        bytes_to_write.append(&mut t);
        bytes_to_write.append(&mut c);

        // Write the vector to memory.

        pm_regions.write(which_log as usize, ABSOLUTE_POS_OF_LEVEL1_METADATA, bytes_to_write.as_slice());

        proof {
            // We want to prove that if we parse the result of
            // flushing memory, we get the desired metadata. The proof
            // is in two parts.

            // Part 1:
            // Prove that if we extract pieces of the flushed memory,
            // we get the little-endian encodings of the desired
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            let mem = pm_regions@[which_log as int].flush().committed();
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL1_METADATA as int, LENGTH_OF_LEVEL1_METADATA as int)
                   =~= level1_metadata);
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL1_CRC as int, CRC_SIZE as int)
                   =~= level1_crc);
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL2_METADATA as int, LENGTH_OF_LEVEL2_METADATA as int)
                   =~= level2_metadata);
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL2_CRC as int, CRC_SIZE as int)
                   =~= level2_crc);
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL3_CDB as int, CRC_SIZE as int)
                   =~= spec_u64_to_le_bytes(CDB_FALSE));
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL3_METADATA_FOR_CDB_FALSE as int,
                                 LENGTH_OF_LEVEL3_METADATA as int)
                   =~= level3_metadata);
            assert (extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL3_CRC_FOR_CDB_FALSE as int, CRC_SIZE as int)
                    =~= level3_crc);

            // Part 2:
            // Prove that if we parse the little-endian-encoded value
            // of the CDB, we get the value that was encoded. This
            // involves invoking the lemma that says the `to` and
            // `from` functions for `u64` are inverses.

            lemma_auto_spec_u64_to_from_le_bytes();
        }
    }

    // This exported executable function writes to persistent memory
    // all the metadata necessary to set up a multilog. To do so, it
    // needs some parameters:
    //
    // `region_sizes`: for each region, how big it is
    //
    // `log_capacities`: for each region, what its capacity will be.
    // Note that this parameter is ghost because it's only needed to
    // establish the postcondition described below.
    //
    // `multilog_id`: the GUID of the multilog it's being used for
    //
    // It also needs the parameter `pm_regions` that gives the
    // persistent memory regions for us to write to.
    //
    // The main postcondition is:
    //
    // ```
    // recover_all(pm_regions@.committed(), multilog_id) ==
    //     Some(AbstractMultiLogState::initialize(log_capacities))
    // ```
    //
    // This means that if the recovery routine runs afterward, then
    // the resulting recovered abstract state will be the valid
    // initial value
    // `AbstractMultiLogState::initialize(log_capacities)`.
    pub fn write_setup_metadata_to_all_regions<PMRegions: PersistentMemoryRegions>(
        pm_regions: &mut PMRegions,
        region_sizes: &Vec<u64>,
        Ghost(log_capacities): Ghost<Seq<u64>>,
        multilog_id: u128
    )
        requires
            old(pm_regions).inv(),
            old(pm_regions)@.len() == region_sizes@.len() == log_capacities.len(),
            1 <= old(pm_regions)@.len() <= u32::MAX,
            forall |i: int| 0 <= i < old(pm_regions)@.len() ==> #[trigger] old(pm_regions)@[i].len() == region_sizes@[i],
            forall |i: int| 0 <= i < old(pm_regions)@.len() ==>
                #[trigger] old(pm_regions)@[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            forall |i: int| 0 <= i < old(pm_regions)@.len() ==>
                #[trigger] old(pm_regions)@[i].len() == log_capacities[i] + ABSOLUTE_POS_OF_LOG_AREA,
            old(pm_regions)@.no_outstanding_writes(),
        ensures
            pm_regions.inv(),
            pm_regions.constants() == old(pm_regions).constants(),
            pm_regions@.len() == old(pm_regions)@.len(),
            forall |i: int| 0 <= i < pm_regions@.len() ==> #[trigger] pm_regions@[i].len() == old(pm_regions)@[i].len(),
            pm_regions@.no_outstanding_writes(),
            recover_all(pm_regions@.committed(), multilog_id) == Some(AbstractMultiLogState::initialize(log_capacities))
    {
        // Loop `which_log` from 0 to `region_sizes.len() - 1`, each time
        // setting up the metadata for region `which_log`.

        let num_logs = region_sizes.len() as u32;
        for which_log in 0..num_logs
            invariant
                num_logs == pm_regions@.len(),
                pm_regions.inv(),
                pm_regions.constants() == old(pm_regions).constants(),
                pm_regions@.len() == old(pm_regions)@.len() == region_sizes@.len() == log_capacities.len(),
                pm_regions@.len() >= 1,
                pm_regions@.len() <= u32::MAX,
                forall |i: int| 0 <= i < pm_regions@.len() ==> #[trigger] pm_regions@[i].len() == old(pm_regions)@[i].len(),
                forall |i: int| 0 <= i < pm_regions@.len() ==> #[trigger] pm_regions@[i].len() == region_sizes@[i],
                forall |i: int| 0 <= i < pm_regions@.len() ==>
                    #[trigger] pm_regions@[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
                forall |i: int| 0 <= i < pm_regions@.len() ==> #[trigger] pm_regions@[i].len() ==
                    log_capacities[i] + ABSOLUTE_POS_OF_LOG_AREA,
                forall |i: int| which_log <= i < pm_regions@.len() ==> #[trigger] pm_regions@[i].no_outstanding_writes(),
                // The key invariant is that every region less than `which_log` has been set up correctly.
                forall |i: u32| i < which_log ==>
                    memory_correctly_set_up_on_single_region(#[trigger] pm_regions@[i as int].flush().committed(),
                                                             region_sizes@[i as int], multilog_id, num_logs, i)
        {
            let region_size: u64 = region_sizes[which_log as usize];
            assert (region_size == pm_regions@[which_log as int].len());
            write_setup_metadata_to_single_region(pm_regions, region_size, multilog_id, num_logs, which_log);
        }

        proof {
            // First, establish that recovering after a flush will get
            // abstract state
            // `AbstractMultiLogState::initialize(log_capacities)`.

            let pm_regions_committed = pm_regions@.flush().committed();
            assert(recover_all(pm_regions_committed, multilog_id)
                   =~= Some(AbstractMultiLogState::initialize(log_capacities))) by {
                assert(forall |i: int| 0 <= i < pm_regions_committed.len() ==>
                       #[trigger] pm_regions_committed[i].len() == pm_regions@[i as int].len());
                assert(forall |i| 0 <= i < pm_regions@.len() ==>
                       #[trigger] pm_regions_committed[i] == pm_regions@[i as int].flush().committed());
                assert(forall |i| 0 <= i < pm_regions_committed.len() ==>
                       extract_log(#[trigger] pm_regions_committed[i], log_capacities[i] as int, 0int, 0int)
                       =~= Seq::<u8>::empty());
            }

            // Second, establish that the flush we're about to do
            // won't change regions' lengths.
            assert(forall |i| 0 <= i < pm_regions@.len() ==> pm_regions@[i].len() == #[trigger] pm_regions@.flush()[i].len());
        }

        pm_regions.flush();
    }

}
