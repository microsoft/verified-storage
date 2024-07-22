use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_mod_bound;
use crate::log2::inv_v::*;
use crate::log2::logspec_t::*;
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
        recover_cdb(pm_region@.committed(), log_start_addr as nat).is_Some(),
        pm_region@.no_outstanding_writes(),
        pm_region@.len() >= log_start_addr + log_size,
        log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
        metadata_types_set(pm_region@.committed(), log_start_addr),
    ensures
        match result {
            Ok(b) => Some(b) == recover_cdb(pm_region@.committed(), log_start_addr as nat),
            // To make sure this code doesn't spuriously generate CRC-mismatch errors,
            // it's obligated to prove that it won't generate such an error when
            // the persistent memory is impervious to corruption.
            Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
            Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
        }
{
    let ghost mem = pm_region@.committed();
    let ghost log_cdb_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| log_start_addr + i);

    let ghost true_cdb_bytes = extract_bytes(mem, log_start_addr as nat, u64::spec_size_of());
    // check_cdb does not require that the true bytes be contiguous, so we need to make Z3 confirm that the 
    // contiguous region we are using as the true value matches the address sequence we pass in.
    assert(true_cdb_bytes == Seq::new(u64::spec_size_of() as nat, |i: int| mem[log_cdb_addrs[i]]));

    let log_cdb = match pm_region.read_aligned::<u64>(log_start_addr) {
        Ok(log_cdb) => log_cdb,
        Err(e) => return Err(LogErr::PmemErr{ err: e }),
    };
    
    let result = check_cdb(log_cdb, Ghost(mem),
                            Ghost(pm_region.constants().impervious_to_corruption),
                            Ghost(log_cdb_addrs));
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
        pm_region@.no_outstanding_writes(),
        metadata_types_set(pm_region@.committed(), log_start_addr),
        log_start_addr + log_size <= pm_region@.len() <= u64::MAX,
        cdb == spec_check_log_cdb(pm_region@.committed(), log_start_addr as nat).unwrap(),
        log_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
    ensures
        ({
            let state = recover_given_cdb(pm_region@.committed(), log_start_addr as nat, log_size as nat, cdb);
            match result {
                Ok(info) => state.is_Some() ==> {
                    &&& metadata_consistent_with_info(pm_region@, log_start_addr, log_size, cdb, info)
                    &&& info_consistent_with_log_area_in_region(pm_region@, log_start_addr, log_size, info, state.unwrap())
                },
                Err(LogErr::CRCMismatch) =>
                    state.is_Some() ==> !pm_region.constants().impervious_to_corruption,
                Err(LogErr::StartFailedDueToInvalidMemoryContents) =>
                    state is None,
                _ => false,
            }
        })
    {
        let ghost mem = pm_region@.committed();
        let ghost state = recover_given_cdb(pm_region@.committed(), log_start_addr as nat, log_size as nat, cdb);
        reveal(spec_padding_needed);

        let log_metadata_pos = get_active_log_metadata_pos(cdb) + log_start_addr;
        let log_crc_pos = get_active_log_crc_pos(cdb) + log_start_addr;
        let ghost true_log_metadata = LogMetadata::spec_from_bytes(extract_bytes(mem, log_metadata_pos as nat, LogMetadata::spec_size_of()));
        let ghost true_crc = u64::spec_from_bytes(extract_bytes(mem, log_crc_pos as nat, u64::spec_size_of()));
        let ghost log_metadata_addrs = Seq::new(LogMetadata::spec_size_of() as nat, |i: int| log_metadata_pos + i);
        let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| log_crc_pos + i);
        let ghost true_bytes = Seq::new(log_metadata_addrs.len(), |i: int| mem[log_metadata_addrs[i] as int]);
        let ghost true_crc_bytes = Seq::new(crc_addrs.len(), |i: int| mem[crc_addrs[i] as int]);

        assert(pm_region@.committed().subrange(log_metadata_pos as int, log_metadata_pos + LogMetadata::spec_size_of()) == true_bytes);
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

        assert(true_log_metadata.spec_to_bytes() == true_bytes && true_crc.spec_to_bytes() == true_crc_bytes);

        if !check_crc(log_metadata.as_slice(), log_crc.as_slice(), Ghost(mem),
                                   Ghost(pm_region.constants().impervious_to_corruption),
                                    Ghost(log_metadata_addrs), Ghost(crc_addrs)) {
            return Err(LogErr::CRCMismatch);
        }

        let log_metadata = log_metadata.extract_init_val(
            Ghost(true_log_metadata), 
            Ghost(true_bytes),
            Ghost(pm_region.constants().impervious_to_corruption)
        );

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

        Ok(LogInfo{
            log_area_len: log_area_length,
            head,
            head_log_area_offset,
            log_length,
            log_plus_pending_length: log_length
        })
    }
}