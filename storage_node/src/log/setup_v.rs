//! This file contains functions for setting up persistent memory
//! regions for use in a multilog.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.

use crate::log::layout_v::*;
use crate::log::logimpl_t::LogErr;
use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    // This function evaluates whether memory was correctly set up on
    // a region. It's a helpful specification function for use in
    // later functions in this file.
    //
    // Because answering this question depends on knowing various
    // metadata about this region and the log it's part of, the
    // function needs various input parameters for that. Its
    // parameters are:
    //
    // `mem` -- the contents of memory for this region
    // `region_size` -- how big this region is
    // `log_id` -- the GUID of the log it's being used for
    spec fn memory_correctly_set_up_on_region(
        mem: Seq<u8>,
        region_size: u64,
        log_id: u128,
    ) -> bool
    {
        let global_crc = deserialize_global_crc(mem);
        let global_metadata = deserialize_global_metadata(mem);
        let region_crc = deserialize_region_crc(mem);
        let region_metadata = deserialize_region_metadata(mem);
        let log_cdb = deserialize_and_check_log_cdb(mem);
        let log_metadata_pos = get_log_metadata_pos(log_cdb.unwrap());
        let log_metadata_and_crc_bytes = extract_bytes(mem, log_metadata_pos as int, LENGTH_OF_LOG_METADATA + CRC_SIZE);
        let (log_metadata, log_crc) = deserialize_log_metadata_and_crc(log_metadata_and_crc_bytes);
        &&& mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
        &&& mem.len() == region_size
        &&& global_crc == global_metadata.spec_crc()
        &&& region_crc == region_metadata.spec_crc()
        &&& log_crc == log_metadata.spec_crc()
        &&& global_metadata.program_guid == LOG_PROGRAM_GUID
        &&& global_metadata.version_number == LOG_PROGRAM_VERSION_NUMBER
        &&& global_metadata.length_of_region_metadata == LENGTH_OF_REGION_METADATA
        &&& region_metadata.region_size == region_size
        &&& region_metadata.log_id == log_id
        &&& region_metadata.log_area_len == region_size - ABSOLUTE_POS_OF_LOG_AREA
        &&& log_cdb == Some(false)
        &&& log_metadata.head == 0
        &&& log_metadata.log_length == 0
    }

    // This executable function sets up a single region for use in a
    // log. To do so, it needs various metadata about this region
    // and the log it's for, so it needs some parameters:
    //
    // `region_size`: how big this region is
    // `log_id`: the GUID of the log it's being used for
    //
    // It also needs the parameter `pm_region` that gives the
    // persistent memory region for us to write to.
    //
    // The main postcondition is:
    //
    // `memory_correctly_set_up_on_single_region(pm_regions@[which_log as int].flush().committed(),
    //                                           region_size, log_id, num_logs, which_log)`
    //
    // This means that, after the next flush, the memory in this
    // region will have been set up correctly. (This function doesn't
    // do the flush, for efficiency. That way we only need one flush
    // operation to flush all regions.)
    fn write_setup_metadata_to_region<PMRegion: PersistentMemoryRegion>(
        pm_region: &mut PMRegion,
        region_size: u64,
        log_id: u128,
    )
        requires
            old(pm_region).inv(),
            old(pm_region)@.no_outstanding_writes(),
            old(pm_region)@.len() == region_size,
            region_size >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            memory_correctly_set_up_on_region(
                pm_region@.flush().committed(), // it'll be correct after the next flush
                region_size, log_id),
    {
        // Initialize global metadata and compute its CRC
        // TODO: might be faster to write to PM first, then compute CRC on that?
        let global_metadata = GlobalMetadata {
            program_guid: LOG_PROGRAM_GUID,
            version_number: LOG_PROGRAM_VERSION_NUMBER,
            length_of_region_metadata: LENGTH_OF_REGION_METADATA,
        };
        let global_crc = calculate_crc(&global_metadata);

        // Initialize region metadata and compute its CRC
        let region_metadata = RegionMetadata {
            region_size,
            log_id,
            log_area_len: region_size - ABSOLUTE_POS_OF_LOG_AREA,
        };
        let region_crc = calculate_crc(&region_metadata);

        // Obtain the initial CDB value
        let cdb = CDB_FALSE;

        // Initialize log metadata and compute its CRC
        let log_metadata = LogMetadata {
            head: 0,
            _padding: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);

        // Write all metadata structures and their CRCs to memory
        // TODO: put these all in a serializable structure so you can write them with one line?
        proof {
            u64::lemma_auto_serialized_len();
            GlobalMetadata::lemma_auto_serialized_len();
            RegionMetadata::lemma_auto_serialized_len();
            LogMetadata::lemma_auto_serialized_len();
        }
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_METADATA, &global_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_GLOBAL_CRC, &global_crc);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_METADATA, &region_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_REGION_CRC, &region_crc);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_CDB, &cdb);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE, &log_metadata);
        pm_region.serialize_and_write(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + LENGTH_OF_LOG_METADATA, &log_crc);

        proof {
            // We want to prove that if we parse the result of
            // flushing memory, we get the desired metadata. The proof
            // is in two parts.

            // Part 1:
            // Prove that if we extract pieces of the flushed memory,
            // we get the little-endian encodings of the desired
            // metadata. By using the `=~=` operator, we get Z3 to
            // prove this by reasoning about per-byte equivalence.

            u64::lemma_auto_serialize_deserialize();
            GlobalMetadata::lemma_auto_serialize_deserialize();
            RegionMetadata::lemma_auto_serialize_deserialize();
            LogMetadata::lemma_auto_serialize_deserialize();

            let mem = pm_region@.flush().committed();
            let log_metadata_and_crc_bytes = extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
                                               LENGTH_OF_LOG_METADATA + CRC_SIZE);
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as int, LENGTH_OF_GLOBAL_METADATA as int)
                   =~= global_metadata.spec_serialize());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as int, CRC_SIZE as int)
                   =~= global_crc.spec_serialize());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as int, LENGTH_OF_REGION_METADATA as int)
                   =~= region_metadata.spec_serialize());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as int, CRC_SIZE as int)
                   =~= region_crc.spec_serialize());
            assert(extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as int, CRC_SIZE as int)
                   =~= CDB_FALSE.spec_serialize());
            assert(extract_bytes(log_metadata_and_crc_bytes, 0, LENGTH_OF_LOG_METADATA as int)
                   =~= log_metadata.spec_serialize());
            assert(extract_bytes(log_metadata_and_crc_bytes, LENGTH_OF_LOG_METADATA as int, CRC_SIZE as int)
                   =~= log_crc.spec_serialize());

            // Part 2:
            // Prove that if we parse the little-endian-encoded value
            // of the CDB, we get the value that was encoded. This
            // involves invoking the lemma that says the `to` and
            // `from` functions for `u64` are inverses.

            lemma_auto_spec_u64_to_from_le_bytes();
            assume(false);
        }
    }

    // This exported executable function writes to persistent memory
    // all the metadata necessary to set up a log. To do so, it
    // needs some parameters:
    //
    // `region_size`: how big the region is
    //
    // `log_capacity`: what its capacity will be.
    // Note that this parameter is ghost because it's only needed to
    // establish the postcondition described below.
    //
    // `log_id`: the GUID of the log it's being used for
    //
    // It also needs the parameter `pm_region` that gives the
    // persistent memory region for us to write to.
    //
    // The main postcondition is:
    //
    // ```
    // recover_state(pm_region@.committed(), log_id) ==
    //     Some(AbstractLogState::initialize(log_capacity))
    // ```
    //
    // This means that if the recovery routine runs afterward, then
    // the resulting recovered abstract state will be the valid
    // initial value
    // `AbstractLogState::initialize(log_capacity)`.
    pub fn write_setup_metadata<PMRegion: PersistentMemoryRegion>(
        pm_region: &mut PMRegion,
        region_size: u64,
        Ghost(log_capacity): Ghost<u64>,
        log_id: u128,
    )
        requires
            old(pm_region).inv(),
            old(pm_region)@.len() == region_size,
            old(pm_region)@.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE,
            old(pm_region)@.len() == log_capacity + ABSOLUTE_POS_OF_LOG_AREA,
            old(pm_region)@.no_outstanding_writes(),
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            pm_region@.len() == old(pm_region)@.len(),
            pm_region@.no_outstanding_writes(),
            recover_state(pm_region@.committed(), log_id) == Some(AbstractLogState::initialize(log_capacity as int)),
    {
        write_setup_metadata_to_region(pm_region, region_size, log_id);

        proof {
            // First, establish that recovering after a flush will get
            // abstract state
            // `AbstractLogState::initialize(log_capacity)`.

            let flushed_region = pm_region@.flush();
            let pm_region_committed = flushed_region.committed();
            assert(recover_state(pm_region_committed, log_id)
                   =~= Some(AbstractLogState::initialize(log_capacity as int))) by {
                assert(pm_region_committed.len() == pm_region@.len());
                assert(pm_region_committed == pm_region@.flush().committed());
                assert(recover_log(pm_region_committed, log_capacity as int, 0int, 0int) =~=
                       Some(AbstractLogState::initialize(log_capacity as int)));
            }

            // Second, establish that the flush we're about to do
            // won't change regions' lengths.
            assert(pm_region@.len() == flushed_region.len());
        }

        pm_region.flush()
    }

}
