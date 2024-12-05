use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::log2::inv_v::*;
use crate::log2::logimpl_v::*;
use crate::log2::layout_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::subregion_v::*;


verus! {

// This exported function reads the corruption-detecting boolean
// and returns it.
//
// `pm_region` -- the persistent-memory region to read from
//
// The result is a `Result<bool, LogErr>` with the following meanings:
//
// `Err(LogErr::CRCMismatch)` -- The CDB couldn't be read due
// to a CRC error.
//
// `Ok(b)` -- The CDB could be read and represents the boolean `b`.
pub fn read_cdb<PMRegion: PersistentMemoryRegion>(pm_region: &PMRegion, log_start_addr: u64, log_size: u64) -> (result: Result<bool, LogErr>)
    requires
        pm_region.inv(),
        recover_cdb(pm_region@.durable_state, log_start_addr as nat).is_Some(),
        pm_region@.flush_predicted(),
        pm_region@.len() >= log_start_addr + log_size,
        log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
        metadata_types_set(pm_region@.durable_state, log_start_addr as nat),
    ensures
        match result {
            Ok(b) => Some(b) == recover_cdb(pm_region@.durable_state, log_start_addr as nat),
            // To make sure this code doesn't spuriously generate CRC-mismatch errors,
            // it's obligated to prove that it won't generate such an error when
            // the persistent memory is impervious to corruption.
            Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption(),
            Err(_) => false,
        }
{
    let ghost mem = pm_region@.durable_state;
    let ghost log_cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| log_start_addr + i);

    let ghost true_cdb_bytes = extract_bytes(mem, log_start_addr as nat, u64::spec_size_of());
    // check_cdb does not require that the true bytes be contiguous, so we need to make Z3 confirm that the 
    // contiguous region we are using as the true value matches the address sequence we pass in.
    assert(true_cdb_bytes == Seq::new(u64::spec_size_of() as nat, |i: int| mem[log_cdb_addrs[i]]));

    let log_cdb = match pm_region.read_aligned::<u64>(log_start_addr) {
        Ok(log_cdb) => log_cdb,
        Err(e) => return Err(LogErr::PmemErr{ err: e }),
    };
    
    let result = check_cdb(log_cdb, Ghost(true_cdb_bytes),
                           Ghost(pm_region.constants()),
                           Ghost(log_start_addr as int));
    match result {
        Some(b) => Ok(b),
        None => Err(LogErr::CRCMismatch)
    }
}

pub fn read_log_variables<PMRegion: PersistentMemoryRegion>(
    pm_region: &PMRegion,
    log_start_addr: u64,
    log_size: u64,
    cdb: bool,
) -> (result: Result<LogInfo, LogErr>)
    requires
        pm_region.inv(),
        pm_region@.flush_predicted(),
        metadata_types_set(pm_region@.durable_state, log_start_addr as nat),
        log_start_addr + log_size <= pm_region@.len() <= u64::MAX,
        cdb == spec_check_log_cdb(pm_region@.durable_state, log_start_addr as nat).unwrap(),
        log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
    ensures
        ({
            let state = recover_given_cdb(pm_region@.durable_state, log_start_addr as nat, log_size as nat, cdb);
            match result {
                Ok(info) => state.is_Some() ==> {
                    &&& metadata_consistent_with_info(pm_region@, log_start_addr as nat, log_size as nat, cdb, info, false)
                    &&& info_consistent_with_log_area(pm_region@, log_start_addr as nat, log_size as nat, info,
                                                    state.unwrap(), false)
                },
                Err(LogErr::CRCMismatch) =>
                    state.is_Some() ==> !pm_region.constants().impervious_to_corruption(),
                Err(LogErr::StartFailedDueToInvalidMemoryContents) =>
                    state is None,
                _ => false,
            }
        })
    {
        let ghost mem = pm_region@.durable_state;
        let ghost state = recover_given_cdb(pm_region@.durable_state, log_start_addr as nat, log_size as nat, cdb);
        reveal(spec_padding_needed);

        let log_metadata_pos = get_active_log_metadata_pos(cdb) + log_start_addr;
        let log_crc_pos = get_active_log_crc_pos(cdb) + log_start_addr;
        let ghost true_log_metadata_bytes = extract_bytes(mem, log_metadata_pos as nat, LogMetadata::spec_size_of());
        let ghost true_log_metadata = LogMetadata::spec_from_bytes(true_log_metadata_bytes);

        assert(pm_region@.durable_state.subrange(log_metadata_pos as int,
                                                 log_metadata_pos + LogMetadata::spec_size_of()) ==
               true_log_metadata_bytes);
        let log_metadata = match pm_region.read_aligned::<LogMetadata>(log_metadata_pos) {
            Ok(log_metadata) => log_metadata,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };
        let log_crc = match pm_region.read_aligned::<u64>(log_crc_pos) {
            Ok(log_crc) => log_crc,
            Err(e) => {
                assert(false);
                return Err(LogErr::PmemErr { err: e });
            }
        };

        assert(true_log_metadata.spec_to_bytes() == true_log_metadata_bytes);

        if !check_crc(log_metadata.as_slice(), log_crc.as_slice(), Ghost(true_log_metadata_bytes),
                      Ghost(pm_region.constants()),
                      Ghost(log_metadata_pos as int),
                      Ghost(log_crc_pos as int)) {
            return Err(LogErr::CRCMismatch);
        }

        let log_metadata = log_metadata.extract_init_val(Ghost(true_log_metadata));

        // Check the log metadata for validity. If it isn't valid,
        // e.g., due to the log length being greater than the log area
        // length, then return an error. Such invalidity can't happen
        // if the persistent memory is recoverable.

        let head = log_metadata.head;
        let log_length = log_metadata.log_length;
        let log_area_length = log_size - log_area_pos();
        if log_length > log_area_length {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }
        if log_length as u128 > u128::MAX - head {
            assert(state.is_None()); // This can't happen if the persistent memory is recoverable
            return Err(LogErr::StartFailedDueToInvalidMemoryContents)
        }

        // Compute the offset into the log area where the head of the
        // log is. This is the u128 `head` mod the u64
        // `log_area_len`. To prove that this will fit in a `u64`, we
        // need to invoke a math lemma saying that the result of a
        // modulo operation is always less than the divisor.

        proof { lemma_mod_bound(head as int, log_area_length as int); }
        let head_log_area_offset: u64 = (head % log_area_length as u128) as u64;

        // Return the log info. This necessitates computing the
        // pending tail position relative to the head, but this is
        // easy: It's the same as the log length. This is because,
        // upon recovery, there are no pending appends beyond the tail
        // of the log.

        let info = LogInfo{
            log_area_len: log_area_length,
            head,
            head_log_area_offset,
            log_length,
            log_plus_pending_length: log_length
        };
        Ok(info)
    }
}
