use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::log2::layout_v::*;


verus! {
    pub exec fn setup2<PM, K>(
        pm_region: &mut PM,
        log_start_addr: u64,
        log_size: u64, 
        log_id: u128,
    ) -> (result: Result<(), crate::kv::kvimpl_t::KvError<K>>) 
        where 
            PM: PersistentMemoryRegion,
            K: std::fmt::Debug,
        requires 
            old(pm_region).inv(),
            log_start_addr + log_size <= old(pm_region)@.len() <= u64::MAX,
            old(pm_region)@.no_outstanding_writes_in_range(log_start_addr as int, log_start_addr + log_size),
            ({
                // LogMetadata size + CDB size + 2 CRC size (1 for each metadata)
                // pos of log area is relative to log_start_addr
                let pos_of_log_area = LogMetadata::spec_size_of() * 2 + u64::spec_size_of() * 2 + u64::spec_size_of();
                log_size >= pos_of_log_area + MIN_LOG_AREA_SIZE
            })
        ensures 
            pm_region.inv(),
            ({
                // Bytes outside the specified log region have not changed
                let old_pm_bytes = old(pm_region)@.flush().committed();
                let new_pm_bytes = pm_region@.flush().committed();
                &&& extract_bytes(new_pm_bytes, 0, log_start_addr as nat) == extract_bytes(old_pm_bytes, 0, log_start_addr as nat)
                &&& extract_bytes(new_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat) == 
                        extract_bytes(old_pm_bytes, (log_start_addr + log_size) as nat, (pm_region@.len() - (log_start_addr + log_size)) as nat)
            })
            
    {
        // Initialize CDB and log metadata
        let log_metadata = LogMetadata {
            head: 0,
            log_length: 0
        };
        let log_crc = calculate_crc(&log_metadata);
        let cdb = CDB_FALSE;

        pm_region.serialize_and_write(log_start_addr, &cdb);
        pm_region.serialize_and_write(log_start_addr + size_of::<u64>() as u64, &log_metadata);
        pm_region.serialize_and_write(log_start_addr + size_of::<u64>() as u64 + size_of::<LogMetadata>() as u64, &log_crc);

        proof { lemma_establish_extract_bytes_equivalence(old(pm_region)@.flush().committed(), pm_region@.flush().committed()); }
    
        Ok(())
    }
}

