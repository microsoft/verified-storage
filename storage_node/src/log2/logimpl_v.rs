use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::inv_v::lemma_subrange_of_extract_bytes_equal;
use crate::kv::kvimpl_t::KvError;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::log2::layout_v::*;
use crate::log2::logspec_t::*;
use crate::log2::start_v::*;
use crate::pmem::wrpm_t::WriteRestrictedPersistentMemoryRegion;

verus! {

// This enumeration represents the various errors that can be
// returned from log operations. They're self-explanatory.
#[derive(Debug)]
pub enum LogErr {
    InsufficientSpaceForSetup { required_space: u64 },
    StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
    StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
    StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
    StartFailedDueToInvalidMemoryContents,
    CRCMismatch,
    InsufficientSpaceForAppend { available_space: u64 },
    CantReadBeforeHead { head: u128 },
    CantReadPastTail { tail: u128 },
    CantAdvanceHeadPositionBeforeHead { head: u128 },
    CantAdvanceHeadPositionBeyondTail { tail: u128 },
    PmemErr { err: PmemError } 
}

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

impl LogInfo {
    pub open spec fn tentatively_append(self, num_bytes: u64) -> Self
    {
        Self{ log_plus_pending_length: (self.log_plus_pending_length + num_bytes) as u64, ..self }
    }
}

pub struct UntrustedLogImpl {
    cdb: bool,
    info: LogInfo,
    state: Ghost<AbstractLogState>
}

impl UntrustedLogImpl {
    pub open spec fn recover(mem: Seq<u8>, log_start_addr: nat, log_size: nat) -> Option<AbstractLogState> 
    {
        recover_state(mem, log_start_addr, log_size)
    }

    // This function specifies how to view the in-memory state of
    // `self` as an abstract log state.
    pub closed spec fn view(&self) -> AbstractLogState
    {
        self.state@
    }

    pub closed spec fn inv<PM>(self, pm: PM) -> bool
        where 
            PM: PersistentMemoryRegion
    {
        true
        // &&& no_outstanding_writes_to_metadata(pm@)
        // &&& memory_matches_deserialized_cdb(pm@, self.cdb)
        // &&& metadata_consistent_with_info(pm@, self.cdb, self.info)
        // &&& info_consistent_with_log_area_in_region(pm@, self.info, self.state@)
        // &&& can_only_crash_as_state(pm@, self.state@.drop_pending_appends())
        // &&& metadata_types_set(pm@.committed())
    }

    pub exec fn setup<PM, K>(
        pm_region: &mut PM,
        log_start_addr: u64,
        log_size: u64, 
    ) -> (result: Result<(), crate::kv::kvimpl_t::KvError<K>>) 
        where 
            PM: PersistentMemoryRegion,
            K: std::fmt::Debug,
        requires 
            old(pm_region).inv(),
            log_start_addr + log_size <= old(pm_region)@.len() <= u64::MAX,
            old(pm_region)@.no_outstanding_writes_in_range(log_start_addr as int, log_start_addr + log_size),
            log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE
        ensures 
            pm_region.inv(),
            ({
                // Bytes outside the specified log region have not changed
                let old_pm_bytes = old(pm_region)@.flush().committed();
                let new_pm_bytes = pm_region@.flush().committed();
                &&& extract_bytes(new_pm_bytes, 0, log_start_addr as nat) == extract_bytes(old_pm_bytes, 0, log_start_addr as nat)
                &&& extract_bytes(new_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat) == 
                        extract_bytes(old_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat)
            }),
            match result {
                Ok(()) => {
                    let pm = pm_region@.flush().committed();
                    let state = AbstractLogState::initialize(log_size - spec_log_area_pos());
                    &&& Self::recover(pm, log_start_addr as nat, log_size as nat) matches Some(recovered_state)
                    &&& state == recovered_state
                    &&& pm_region@.len() == old(pm_region)@.len()
                }
                Err(_) => false
            } 
    {
        // Initialize CDB and log metadata
        let log_metadata = LogMetadata {
            head: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);
        let log_cdb = CDB_FALSE;

        assert(spec_log_area_pos() >= spec_log_header_area_size()) by {
            reveal(spec_padding_needed);
        }

        // Write the CDB, metadata, and CRC to PM. Since PM isn't write restricted right now,
        // we don't have to prove that these updates are crash safe.
        pm_region.serialize_and_write(log_start_addr, &log_cdb);
        pm_region.serialize_and_write(log_start_addr + log_header_pos_cdb_false(), &log_metadata);
        pm_region.serialize_and_write(log_start_addr + log_header_pos_cdb_false() + size_of::<LogMetadata>() as u64, &log_crc);

        proof { 
            broadcast use pmcopy_axioms;

            // Prove that we have not modified any bytes that do not fall in the log region
            lemma_establish_extract_bytes_equivalence(old(pm_region)@.flush().committed(), pm_region@.flush().committed()); 

            // Prove that the resulting log, when recovered, is initialized
            let pm = pm_region@.flush().committed();
            let log_region = extract_bytes(pm, log_start_addr as nat, log_size as nat);
            let recovered_state = Self::recover(pm, log_start_addr as nat, log_size as nat);
            
            // Prove that we can recover a valid log
            // First, prove that the return value of recover is not None
            assert(log_region.len() > u64::spec_size_of());

            // Prove that we wrote a valid CDB
            let cdb_bytes = extract_bytes(pm, log_start_addr as nat, u64::spec_size_of());
            assert(cdb_bytes == log_cdb.spec_to_bytes());
            lemma_subrange_of_extract_bytes_equal(pm, log_start_addr as nat, log_start_addr as nat, log_size as nat, u64::spec_size_of());
            let cdb = if log_cdb == CDB_FALSE { false } else { true };

            // Prove that the CRC we wrote matches the metadata that we wrote
            let metadata = spec_get_active_log_metadata(pm, log_start_addr as nat, cdb);
            let metadata_bytes = extract_bytes(pm, (log_start_addr + spec_log_header_pos_cdb_false()) as nat, LogMetadata::spec_size_of());
            let crc = spec_get_active_log_crc(pm, log_start_addr as nat, cdb);
            let crc_bytes = extract_bytes(pm, (log_start_addr + spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()) as nat, u64::spec_size_of());
            assert(metadata_bytes == log_metadata.spec_to_bytes());
            lemma_subrange_of_extract_bytes_equal(pm, log_start_addr as nat, (log_start_addr + spec_log_header_pos_cdb_false()) as nat, log_size as nat, LogMetadata::spec_size_of());
            lemma_subrange_of_extract_bytes_equal(pm, 
                log_start_addr as nat, 
                (log_start_addr + spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()) as nat,
                log_size as nat, 
                u64::spec_size_of());
            assert(crc == metadata.spec_crc());

            // Once we have proven that the log recovers to a valid abstract state, extensional equality takes care of the rest of the proof
            assert(recovered_state is Some);
            assert(recovered_state.unwrap() =~= AbstractLogState::initialize(log_size - spec_log_area_pos()));
        }
    
        Ok(())
    }

    // TODO: rename TrustedKvPermission to TrustedPermission
    // or use a trait
    pub fn start<PM>(
        pm_region: &PM,
        log_start_addr: u64,
        log_size: u64, 
        Ghost(state): Ghost<AbstractLogState>,
    ) -> (result: Result<Self, LogErr>)
        where 
            PM: PersistentMemoryRegion,
        requires
            Self::recover(pm_region@.flush().committed(), log_start_addr as nat, log_size as nat) == Some(state),
            pm_region.inv(),
            pm_region@.no_outstanding_writes(),
            pm_region@.len() >= log_start_addr + log_size,
        ensures
            match result {
                Ok(log_impl) => {
                    &&& log_impl@ == state
                    &&& log_impl.inv(*pm_region)
                }
                Err(_) => false
            }
    {
        // First, we read the corruption-detecting boolean and
        // return an error if that fails.

        let cdb = read_cdb(pm_region, log_start_addr, log_size)?;

        let info = read_log_variables(pm_region, log_start_addr, log_size, cdb)?;

        Ok(Self { cdb, info, state: Ghost(state) })
    }  
}
    
}

