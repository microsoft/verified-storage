//! This file contains functions describing invariants of a
//! `UntrustedMultiLogImpl`, as well as lemmas about those invariants.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!

use crate::log::inv_v::{lemma_auto_smaller_range_of_seq_is_subrange, lemma_active_metadata_bytes_equal_implies_metadata_types_set};
use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_v::LogInfo;
use crate::multilog::multilogspec_t::{AbstractLogState, AbstractMultiLogState};
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use deps_hack::nix::libc::ENOTSUP;
use vstd::prelude::*;

verus! {

    broadcast use pmcopy_axioms;

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

    pub proof fn lemma_no_outstanding_writes_to_metadata_implies_no_outstanding_writes_to_active_metadata(
        pm_regions_view: PersistentMemoryRegionsView, 
        num_logs: u32,
        cdb: bool
    )
        requires 
            no_outstanding_writes_to_metadata(pm_regions_view, num_logs),
            num_logs == pm_regions_view.len(),
            deserialize_and_check_log_cdb(pm_regions_view[0].committed()) is Some,
            cdb == deserialize_and_check_log_cdb(pm_regions_view[0].committed()).unwrap(),
        ensures 
            no_outstanding_writes_to_active_metadata(pm_regions_view, cdb)
    {
        assert(forall |i: u32| is_valid_log_index(i, num_logs) ==> {
            let pm_region_view = #[trigger] pm_regions_view[i as int];
            &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int)
            &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, 
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE + LogMetadata::spec_size_of() + u64::spec_size_of())
            &&& !cdb ==> pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, 
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + LogMetadata::spec_size_of() + u64::spec_size_of())
        });
    }

    pub open spec fn active_metadata_is_equal(
        pm1: PersistentMemoryRegionsView,
        pm2: PersistentMemoryRegionsView
    ) -> bool
    {
        let cdb1 = deserialize_and_check_log_cdb(pm1[0].committed());
        let cdb2 = deserialize_and_check_log_cdb(pm2[0].committed());
        &&& cdb1 is Some
        &&& cdb2 is Some 
        &&& cdb1 == cdb2
        &&& pm1.len() == pm2.len()
        &&& forall |i: int| #![auto] 0 <= i < pm1.len() ==> active_metadata_is_equal_in_region(pm1[i], pm2[i], cdb1.unwrap())
    }

    pub open spec fn active_metadata_is_equal_in_region(
        pm_region_view1: PersistentMemoryRegionView,
        pm_region_view2: PersistentMemoryRegionView,
        cdb: bool
    ) -> bool 
    {
        let pm_bytes1 = pm_region_view1.committed();
        let pm_bytes2 = pm_region_view2.committed();
        active_metadata_bytes_are_equal(pm_bytes1, pm_bytes2, cdb)
    }

    pub open spec fn active_metadata_bytes_are_equal(
        pm_bytes1: Seq<u8>,
        pm_bytes2: Seq<u8>,
        cdb: bool
    ) -> bool {
        &&& pm_bytes1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) ==
                pm_bytes2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) 
        &&& {
            if cdb {
                pm_bytes1.subrange(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE + LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                    pm_bytes2.subrange(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE + LogMetadata::spec_size_of() + u64::spec_size_of()) 
            } else {
                pm_bytes1.subrange(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + LogMetadata::spec_size_of() + u64::spec_size_of()) ==
                    pm_bytes2.subrange(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + LogMetadata::spec_size_of() + u64::spec_size_of()) 
            }
        }
    }

    // This invariant is similar to no_outstanding_writes_to_metadata, except that it allows outstanding writes
    // to the inactive log metadata region.
    pub open spec fn no_outstanding_writes_to_active_metadata(
        pm_regions_view: PersistentMemoryRegionsView,
        cdb: bool
    ) -> bool 
    {
        forall |i: int| #![auto] 0 <= i < pm_regions_view.len() ==> 
            no_outstanding_writes_to_active_metadata_in_region(pm_regions_view[i], cdb)
    }
    
    pub open spec fn no_outstanding_writes_to_active_metadata_in_region(
        pm_region_view: PersistentMemoryRegionView,
        cdb: bool,
    ) -> bool 
    {
        // Note that we include the active log metadata's CRC in the region
        let active_log_metadata_result = if cdb {
            pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int,
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE + LogMetadata::spec_size_of() + u64::spec_size_of())
        } else {
            pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int,
                ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE + LogMetadata::spec_size_of() + u64::spec_size_of())
        };
        &&& pm_region_view.no_outstanding_writes_in_range(ABSOLUTE_POS_OF_GLOBAL_METADATA as int,
                                                        ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int)
        &&& active_log_metadata_result
    }

    // This invariant says that there are no outstanding writes to the
    // CDB area of persistent memory, and that the committed contents
    // of that area correspond to the given boolean `cdb`.
    pub open spec fn memory_matches_cdb(pm_regions_view: PersistentMemoryRegionsView, cdb: bool) -> bool
    {
        &&& pm_regions_view.no_outstanding_writes_in_range(0int, ABSOLUTE_POS_OF_LOG_CDB as int,
                                                         ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
        &&& extract_and_parse_log_cdb(pm_regions_view[0].committed()) == Some(cdb)
    }

    pub open spec fn memory_matches_deserialized_cdb(pm_regions_view: PersistentMemoryRegionsView, cdb: bool) -> bool
    {
        &&& pm_regions_view.no_outstanding_writes_in_range(0int, ABSOLUTE_POS_OF_LOG_CDB as int,
            ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of())
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
        &&& global_metadata.length_of_region_metadata == RegionMetadata::spec_size_of()
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
            new_cdb_bytes.len() == u64::spec_size_of(),
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

    pub open spec fn regions_metadata_types_set(pm_regions: PersistentMemoryRegionsView) -> bool 
    {
        let mems = pm_regions.committed();
        metadata_types_set(mems)
    }

    pub open spec fn metadata_types_set(mems: Seq<Seq<u8>>) -> bool 
    {
        &&& metadata_types_set_in_first_region(mems[0])
        &&& {
            let cdb = deserialize_and_check_log_cdb(mems[0]);
            &&& cdb is Some 
            &&& forall |i: int| #![auto] 1 <= i < mems.len() ==> metadata_types_set_in_region(mems[i], cdb.unwrap())
        }
    }

    pub open spec fn metadata_types_set_in_first_region(mem: Seq<u8>) -> bool 
    {
        &&& exists |cdb: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as int, u64::spec_size_of()) == cdb.spec_to_bytes()
        &&& {
            let cdb = choose |cdb: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as int, u64::spec_size_of())  == cdb.spec_to_bytes();
            &&& cdb == CDB_TRUE || cdb == CDB_FALSE 
            &&& cdb == CDB_TRUE ==> metadata_types_set_in_region(mem, true)
            &&& cdb == CDB_FALSE ==> metadata_types_set_in_region(mem, false)
        }
    }

    pub open spec fn metadata_types_set_in_region(mem: Seq<u8>, cdb: bool) -> bool
    {
        &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as int, u64::spec_size_of()) == crc.spec_to_bytes()
        &&& exists |global_metadata: GlobalMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as int, GlobalMetadata::spec_size_of()) == global_metadata.spec_to_bytes()
        &&& {
            let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as int, u64::spec_size_of()) == crc.spec_to_bytes();
            let metadata = choose |global_metadata: GlobalMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as int, GlobalMetadata::spec_size_of()) == global_metadata.spec_to_bytes();
            crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as int, u64::spec_size_of()) == crc.spec_to_bytes()
        &&& exists |region_metadata: RegionMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as int, RegionMetadata::spec_size_of()) == region_metadata.spec_to_bytes()
        &&& {
            let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as int, u64::spec_size_of()) == crc.spec_to_bytes();
            let metadata = choose |region_metadata: RegionMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as int, RegionMetadata::spec_size_of()) == region_metadata.spec_to_bytes();
            crc == spec_crc_u64(metadata.spec_to_bytes())
        }
        &&& {
            &&& cdb ==> {
                &&& exists |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes()
                &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int, u64::spec_size_of()) == crc.spec_to_bytes()
                &&& {
                    let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int, u64::spec_size_of()) == crc.spec_to_bytes();
                    let metadata = choose |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes();
                    crc == spec_crc_u64(metadata.spec_to_bytes())
                }
            }
            &&& !cdb ==> {
                &&& exists |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes()
                &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int, u64::spec_size_of()) == crc.spec_to_bytes()
                &&& {
                    let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int, u64::spec_size_of()) == crc.spec_to_bytes();
                    let metadata = choose |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes();
                    crc == spec_crc_u64(metadata.spec_to_bytes())
                }
            }
        }
    }

    pub open spec fn inactive_metadata_types_set_in_region(mem: Seq<u8>, cdb: bool) -> bool 
    {
        &&& cdb ==> {
            &&& exists |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes()
                &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int, u64::spec_size_of()) == crc.spec_to_bytes()
                &&& {
                    let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE as int, u64::spec_size_of()) == crc.spec_to_bytes();
                    let metadata = choose |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes();
                    crc == spec_crc_u64(metadata.spec_to_bytes())
                }
        }
        &&& !cdb ==> {
            &&& exists |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes()
                &&& exists |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int, u64::spec_size_of()) == crc.spec_to_bytes()
                &&& {
                    let crc = choose |crc: u64| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE as int, u64::spec_size_of()) == crc.spec_to_bytes();
                    let metadata = choose |log_metadata: LogMetadata| extract_bytes(mem, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE as int, LogMetadata::spec_size_of()) == log_metadata.spec_to_bytes();
                    crc == spec_crc_u64(metadata.spec_to_bytes())
                }
        }
    }

    // This lemma helps us establish that metadata types are set in the a region even when we obtain 
    // a view of its bytes in different ways.
    pub proof fn lemma_metadata_types_set_flush_committed(
        pm_regions_view: PersistentMemoryRegionsView,
        cdb: bool
    )
        ensures 
            forall |i: int| #![auto] {
                &&& 0 < i < pm_regions_view.len() 
                &&& metadata_types_set_in_region(pm_regions_view[i].flush().committed(), cdb) 
            } ==> metadata_types_set_in_region(pm_regions_view.flush().committed()[i], cdb)
    {} 

    pub proof fn lemma_metadata_set_after_crash_in_region(
        pm_region_view: PersistentMemoryRegionView,
        cdb: bool 
    )
        requires 
            no_outstanding_writes_to_active_metadata_in_region(pm_region_view, cdb),
            metadata_types_set_in_region(pm_region_view.committed(), cdb),
            ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < pm_region_view.len()
        ensures 
            forall |s| #![auto] {
                pm_region_view.can_crash_as(s) 
            } ==> metadata_types_set_in_region(s, cdb),
    {
        let pm_bytes = pm_region_view.committed();
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_region_view);

        assert forall |s| #![auto] {
            &&& pm_region_view.can_crash_as(s) 
        } implies metadata_types_set_in_region(s, cdb) by {
            lemma_establish_extract_bytes_equivalence(s, pm_region_view.committed());
        }
    }

    pub proof fn lemma_metadata_set_after_crash_in_first_region(
        pm_regions_view: PersistentMemoryRegionsView,
        cdb: bool 
    )
        requires 
            no_outstanding_writes_to_active_metadata_in_region(pm_regions_view[0], cdb),
            metadata_types_set_in_first_region(pm_regions_view[0].committed()),
            deserialize_and_check_log_cdb(pm_regions_view[0].committed()) is Some,
            cdb == deserialize_and_check_log_cdb(pm_regions_view[0].committed()).unwrap(),
        ensures 
            forall |s| #![auto] {
                &&& pm_regions_view[0].can_crash_as(s) 
                &&& s.len() >= ABSOLUTE_POS_OF_LOG_AREA
            } ==> {
                let cdb2 = deserialize_and_check_log_cdb(s);
                &&& cdb2 is Some
                &&& cdb2.unwrap() == cdb
                &&& metadata_types_set_in_first_region(s)
            }
    {
        let pm_bytes = pm_regions_view[0].committed();
        lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(pm_regions_view[0]);

        assert forall |s| #![auto] {
            &&& pm_regions_view[0].can_crash_as(s) 
            &&& s.len() >= ABSOLUTE_POS_OF_LOG_AREA
        } implies {
            let cdb2 = deserialize_and_check_log_cdb(s);
            &&& cdb2 is Some
            &&& cdb == cdb2.unwrap()
            &&& metadata_types_set_in_first_region(s)
        } by {
            lemma_establish_extract_bytes_equivalence(s, pm_bytes);
            assert(pm_regions_view[0].no_outstanding_writes_in_range(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()));
            assert(pm_bytes.subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()) =~= 
                s.subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()));
        }
    }

    pub proof fn lemma_metadata_set_after_crash(
        pm_regions_view: PersistentMemoryRegionsView,
        cdb: bool
    ) 
        requires 
            no_outstanding_writes_to_active_metadata(pm_regions_view, cdb),
            regions_metadata_types_set(pm_regions_view),
            memory_matches_deserialized_cdb(pm_regions_view, cdb),
            // is this just the same as above...?
            deserialize_and_check_log_cdb(pm_regions_view[0].committed()) is Some,
            cdb == deserialize_and_check_log_cdb(pm_regions_view[0].committed()).unwrap(),
            pm_regions_view.len() > 0,
            forall |i: int| 0 <= i < pm_regions_view.len() ==> 0 <= ABSOLUTE_POS_OF_GLOBAL_METADATA < ABSOLUTE_POS_OF_LOG_AREA < #[trigger] pm_regions_view[i].len()
        ensures 
            forall |s| #![auto] {
                &&& pm_regions_view.can_crash_as(s) 
            } ==> metadata_types_set(s),
    {

        assert(metadata_types_set(pm_regions_view.committed()));
        // Z3 cannot always tell that pm_regions_view[i].committed() == pm_regions_view.committed()[i]; we have to help it out here
        assert forall |i: int| #![auto] 1 <= i < pm_regions_view.len() implies metadata_types_set_in_region(pm_regions_view[i].committed(), cdb) by {
            assert(metadata_types_set_in_region(pm_regions_view.committed()[i], cdb));
        };

        assert forall |s| #![auto] pm_regions_view.can_crash_as(s) implies metadata_types_set(s)
        by {
            assert forall |s| #![auto] pm_regions_view[0].can_crash_as(s) implies {
                let cdb2 = deserialize_and_check_log_cdb(s);
                &&& cdb2 is Some
                &&& cdb2.unwrap() == cdb
                &&& metadata_types_set_in_first_region(s) 
            } by {
                lemma_metadata_set_after_crash_in_first_region(pm_regions_view, cdb);
            }

            assert forall |i, s| #![auto] {
                &&& 1 <= i < pm_regions_view.len()
                &&& pm_regions_view[i].can_crash_as(s)
            } implies metadata_types_set_in_region(s, cdb)
            by {
                lemma_metadata_set_after_crash_in_region(pm_regions_view[i], cdb);
            }
    
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
            bytes_to_write.len() == LogMetadata::spec_size_of(),
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
            bytes_to_write.len() == u64::spec_size_of(),
        ensures
            ({
                let pm_regions_view2 = pm_regions_view.write(
                    which_log as int,
                    get_log_metadata_pos(!cdb) + LogMetadata::spec_size_of(),
                    bytes_to_write
                );
                &&& memory_matches_deserialized_cdb(pm_regions_view2, cdb)
                &&& each_metadata_consistent_with_info(pm_regions_view2, multilog_id, num_logs, cdb, infos)
                &&& each_info_consistent_with_log_area(pm_regions_view2, num_logs, infos, state)
            })
    {
        let pm_regions_view2 = pm_regions_view.write(
            which_log as int,
            get_log_metadata_pos(!cdb) + LogMetadata::spec_size_of(),
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

    pub proof fn lemma_regions_metadata_matches_implies_metadata_types_set(
        pm1: PersistentMemoryRegionsView,
        pm2: PersistentMemoryRegionsView,
        cdb: bool
    )
        requires 
            no_outstanding_writes_to_active_metadata(pm1, cdb),
            no_outstanding_writes_to_active_metadata(pm2, cdb),
            metadata_types_set(pm1.committed()),
            memory_matches_deserialized_cdb(pm1, cdb),
            active_metadata_is_equal(pm1, pm2),
            pm1.len() == pm2.len(),
            pm1.len() > 0,
            forall |i: int| #![auto] 0 <= i < pm1.len() ==> pm1[i].len() == pm2[i].len(),
            forall |i: int| #![auto] 0 <= i < pm1.len() ==> ABSOLUTE_POS_OF_LOG_AREA < pm1[i].len(),
        ensures 
            metadata_types_set(pm2.committed())
    {
        let log_metadata_pos = get_log_metadata_pos(cdb);
        
        lemma_auto_smaller_range_of_seq_is_subrange(pm1[0].committed());
        lemma_auto_smaller_range_of_seq_is_subrange(pm2[0].committed());
        
        assert(metadata_types_set_in_first_region(pm2[0].committed()));
        assert forall |i: int| #![auto] 1 <= i < pm1.len() implies metadata_types_set_in_region(pm2.committed()[i], cdb) by {
            lemma_establish_extract_bytes_equivalence(pm1.committed()[i], pm2.committed()[i]);
            lemma_auto_smaller_range_of_seq_is_subrange(pm1.committed()[i]);
            lemma_auto_smaller_range_of_seq_is_subrange(pm2.committed()[i]);
            assert(pm1[i].committed().subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) == 
                pm2[i].committed().subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int));
            assert(extract_bytes(pm1.committed()[i], ABSOLUTE_POS_OF_GLOBAL_METADATA as int, GlobalMetadata::spec_size_of()) ==
                extract_bytes(pm2.committed()[i], ABSOLUTE_POS_OF_GLOBAL_METADATA as int, GlobalMetadata::spec_size_of()));
            assert(extract_bytes(pm1.committed()[i], ABSOLUTE_POS_OF_GLOBAL_CRC as int, u64::spec_size_of()) ==
                extract_bytes(pm2.committed()[i], ABSOLUTE_POS_OF_GLOBAL_CRC as int, u64::spec_size_of()));
        }
    }

    pub proof fn lemma_metadata_types_set_after_cdb_update(
        old_pm_regions_view: PersistentMemoryRegionsView,
        new_pm_regions_view: PersistentMemoryRegionsView,
        log_id: u128,
        new_cdb_bytes: Seq<u8>,
        old_cdb: bool,
    )
        requires 
            old_pm_regions_view.no_outstanding_writes(),
            new_pm_regions_view.no_outstanding_writes(),
            old_pm_regions_view.len() == new_pm_regions_view.len(),
            new_cdb_bytes == CDB_FALSE.spec_to_bytes() || new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            old_pm_regions_view.len() > 0,
            deserialize_and_check_log_cdb(old_pm_regions_view.committed()[0]) is Some,
            deserialize_and_check_log_cdb(old_pm_regions_view.committed()[0]).unwrap() == old_cdb,
            old_cdb ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
            !old_cdb ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
            new_pm_regions_view =~= old_pm_regions_view.write(0, ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
            metadata_types_set(old_pm_regions_view.committed()),
            forall |i: int| #![auto] 0 <= i < old_pm_regions_view.len() ==> old_pm_regions_view[i].len() == new_pm_regions_view[i].len(),
            forall |i: int| #![auto] 0 <= i < old_pm_regions_view.len() ==> ABSOLUTE_POS_OF_LOG_AREA < old_pm_regions_view[i].len(),
            forall |i: int| #![auto] 0 <= i < old_pm_regions_view.len() ==> inactive_metadata_types_set_in_region(old_pm_regions_view.committed()[i], old_cdb),
        ensures 
            metadata_types_set(new_pm_regions_view.committed())
    {
        lemma_establish_extract_bytes_equivalence(old_pm_regions_view.committed()[0], new_pm_regions_view.committed()[0]);

        // The CDB has been updated in log 0, so its type is set
        assert(new_pm_regions_view.committed()[0].subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()) =~= new_cdb_bytes);

        let new_cdb = deserialize_and_check_log_cdb(new_pm_regions_view.committed()[0]).unwrap();
        let log_metadata_pos = get_log_metadata_pos(new_cdb);

        assert forall |i: int| #![auto] 1 <= i < old_pm_regions_view.len() implies {
            metadata_types_set_in_region(new_pm_regions_view.committed()[i], new_cdb)
        } by {
            lemma_establish_extract_bytes_equivalence(old_pm_regions_view.committed()[i], new_pm_regions_view.committed()[i]);
        }
    }

    pub proof fn lemma_no_outstanding_writes_to_active_metadata_implies_metadata_types_set_after_flush(
        pm_regions_view: PersistentMemoryRegionsView,
        cdb: bool,
    ) 
        requires 
            cdb == deserialize_and_check_log_cdb(pm_regions_view[0].committed()).unwrap(),
            no_outstanding_writes_to_active_metadata(pm_regions_view, cdb),
            metadata_types_set(pm_regions_view.committed()),
        ensures 
            metadata_types_set(pm_regions_view.flush().committed()),
    {
        assume(false);
    }

    // pub proof fn lemma_region_metadata_matches_implies_metadata_types_set(
    //     pm1: PersistentMemoryRegionView,
    //     pm2: PersistentMemoryRegionView,
    //     cdb: bool
    // )
    //     requires 
    //         no_outstanding_writes_to_active_metadata(pm1, cdb),
    //         no_outstanding_writes_to_active_metadata(pm2, cdb),
    //         metadata_types_set(pm1.committed()),
    //         memory_matches_deserialized_cdb(pm1, cdb),
    //         0 < ABSOLUTE_POS_OF_LOG_AREA < pm1.committed().len(),
    //         0 < ABSOLUTE_POS_OF_LOG_AREA < pm2.committed().len(),
    //         active_metadata_is_equal(pm1, pm2),
    //         pm1.len() == pm2.len()
    //     ensures 
    //         metadata_types_set(pm2.committed())
    // {
    //     lemma_active_metadata_bytes_equal_implies_metadata_types_set(pm1.committed(), pm2.committed(), cdb);
    // }

    // // This lemma proves that if two sequences have equal active metadata bytes and one has its metadata types set,
    // // then the other sequence also has its metadata types set.
    // pub proof fn lemma_active_metadata_bytes_equal_implies_metadata_types_set(
    //     mem1: Seq<u8>,
    //     mem2: Seq<u8>,
    //     cdb: bool
    // )
    //     requires 
    //         ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
    //         ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
    //         active_metadata_bytes_are_equal(mem1, mem2),
    //         ({
    //             let cdb1 = deserialize_and_check_log_cdb(mem1);
    //             let cdb2 = deserialize_and_check_log_cdb(mem2);
    //             let log_metadata_pos = get_log_metadata_pos(cdb);
    //             &&& cdb1 is Some 
    //             &&& cdb2 is Some 
    //             &&& cdb ==> cdb1.unwrap() && cdb2.unwrap()
    //             &&& !cdb ==> !cdb1.unwrap() && !cdb2.unwrap()
    //         }),
    //         metadata_types_set(mem1)
    //     ensures 
    //         metadata_types_set(mem2),
    // {
    //     lemma_establish_extract_bytes_equivalence(mem1, mem2);

    //     // This lemma automatically establishes the relationship between subranges of subranges from the same sequence, 
    //     // so knowing that the assertions below cover subranges of larger, equal subranges is enough to establish equality
    //     // (but we have to assert it explicitly to hit the triggers)
    //     lemma_auto_smaller_range_of_seq_is_subrange(mem1);

    //     // First, establish that the immutable parts and the CDB are the same between both byte sequences.
    //     let mem1_without_log_metadata = mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int);
    //     let mem2_without_log_metadata = mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int);
    //     assert(mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_GLOBAL_METADATA + GlobalMetadata::spec_size_of()) == 
    //         mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_GLOBAL_METADATA + GlobalMetadata::spec_size_of()));
    //     assert(mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_CRC as int, ABSOLUTE_POS_OF_GLOBAL_CRC + u64::spec_size_of()) == 
    //         mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_CRC as int, ABSOLUTE_POS_OF_GLOBAL_CRC + u64::spec_size_of()));
    //     assert(mem1.subrange(ABSOLUTE_POS_OF_REGION_METADATA as int, ABSOLUTE_POS_OF_REGION_METADATA + RegionMetadata::spec_size_of()) == 
    //         mem2.subrange(ABSOLUTE_POS_OF_REGION_METADATA as int, ABSOLUTE_POS_OF_REGION_METADATA + RegionMetadata::spec_size_of()));
    //     assert(mem1.subrange(ABSOLUTE_POS_OF_REGION_CRC as int, ABSOLUTE_POS_OF_REGION_CRC + u64::spec_size_of()) == 
    //         mem2.subrange(ABSOLUTE_POS_OF_REGION_CRC as int, ABSOLUTE_POS_OF_REGION_CRC + u64::spec_size_of()));
    //     assert(mem1.subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()) == 
    //         mem2.subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()));

    //     // Next, establish that the types are set in the active metadata
    //     let log_metadata_pos = get_log_metadata_pos(cdb);
    //     assert(mem1.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of()) == 
    //         mem2.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of()));
    //     assert(mem1.subrange(log_metadata_pos + LogMetadata::spec_size_of(), log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) ==
    //         mem2.subrange(log_metadata_pos + LogMetadata::spec_size_of(), log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()));
    // }

    // pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
    //     ensures 
    //         forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) 
    // {
    //     assert forall |i: int, j, k: int, l: int| 0 <= i <= k <= l <= j <= mem1.len() implies mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l) by {
    //         lemma_smaller_range_of_seq_is_subrange(mem1, i, j, k, l);
    //     }
    // }

    // pub proof fn lemma_header_bytes_equal_implies_active_metadata_bytes_equal(mem1: Seq<u8>, mem2: Seq<u8>)
    //     requires 
    //         ABSOLUTE_POS_OF_LOG_AREA <= mem1.len(),
    //         ABSOLUTE_POS_OF_LOG_AREA <= mem2.len(),
    //         mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int) =~= 
    //             mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_AREA as int),
    //         deserialize_and_check_log_cdb(mem1) is Some,
    //     ensures 
    //         active_metadata_bytes_are_equal(mem1, mem2)
    // {
    //     lemma_establish_extract_bytes_equivalence(mem1, mem2);

    //     lemma_auto_smaller_range_of_seq_is_subrange(mem1);

    //     let cdb = deserialize_and_check_log_cdb(mem1).unwrap();
    //     let log_metadata_pos = get_log_metadata_pos(cdb);

    //     assert(mem1.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) ==
    //         mem2.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE as int) );
    //     assert(mem1.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) == 
    //         mem2.subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()));
    // }

    // pub proof fn lemma_metadata_types_set_after_cdb_update(
    //     old_pm_region_view: PersistentMemoryRegionView,
    //     new_pm_region_view: PersistentMemoryRegionView,
    //     log_id: u128,
    //     new_cdb_bytes: Seq<u8>,
    //     old_cdb: bool,
    // )
    //     requires 
    //         old_pm_region_view.no_outstanding_writes(),
    //         new_pm_region_view.no_outstanding_writes(),
    //         old_pm_region_view.len() >= ABSOLUTE_POS_OF_LOG_AREA,
    //         old_pm_region_view.len() == new_pm_region_view.len(),
    //         new_cdb_bytes == CDB_FALSE.spec_to_bytes() || new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
    //         old_cdb ==> new_cdb_bytes == CDB_FALSE.spec_to_bytes(),
    //         !old_cdb ==> new_cdb_bytes == CDB_TRUE.spec_to_bytes(),
    //         new_pm_region_view =~= old_pm_region_view.write(ABSOLUTE_POS_OF_LOG_CDB as int, new_cdb_bytes).flush(),
    //         metadata_types_set(old_pm_region_view.committed()),
    //         inactive_metadata_types_set(old_pm_region_view.committed())
    //     ensures 
    //         metadata_types_set(new_pm_region_view.committed())
    // {
    //     let old_mem = old_pm_region_view.committed();
    //     let new_mem = new_pm_region_view.committed();
    //     lemma_auto_smaller_range_of_seq_is_subrange(old_mem);
    //     lemma_auto_smaller_range_of_seq_is_subrange(new_mem);
        
    //     // Immutable metadata has not changed
    //     assert(old_mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_CDB as int) =~=
    //         new_mem.subrange(ABSOLUTE_POS_OF_GLOBAL_METADATA as int, ABSOLUTE_POS_OF_LOG_CDB as int));

    //     // We updated the CDB -- its type is still set, since new_cdb_bytes corresponds to a serialization of a valid CDB value
    //     assert(new_mem.subrange(ABSOLUTE_POS_OF_LOG_CDB as int, ABSOLUTE_POS_OF_LOG_CDB + u64::spec_size_of()) == new_cdb_bytes);

    //     let new_cdb = deserialize_and_check_log_cdb(new_mem).unwrap();
    //     let active_metadata_pos = get_log_metadata_pos(new_cdb);
    //     // The bytes in the new active position are the same in both byte sequences, and they had their metadata types set in the old view,
    //     // so types are also set in the new view, and the postcondition holds.
    //     assert(new_mem.subrange(active_metadata_pos as int, active_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()) == 
    //         old_mem.subrange(active_metadata_pos as int, active_metadata_pos + LogMetadata::spec_size_of() + u64::spec_size_of()));
    // }

}
