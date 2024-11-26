use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::log2::{inv_v::*, logimpl_v::*};
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::util_v::*;
use deps_hack::{PmCopy};

verus! {

    // TODO: this should probably be given by the user/determined based on the size of log entry structs being appended
    // 12 is the minimum size for a validify/delete log entry -- 8 byte address, 8 byte length,
    // and 8 bytes to write
    pub const MIN_LOG_AREA_SIZE: u64 = 24;

    #[repr(C)]
    #[derive(PmCopy, Copy, Default)]
    pub struct LogMetadata {
        pub log_length: u64,
        pub head: u128,
    }

    pub open spec fn spec_log_header_area_size() -> nat {
        // CDB + two LogMetadata + two CRC
        u64::spec_size_of() + LogMetadata::spec_size_of() * 2 + u64::spec_size_of() * 2
    }

    pub exec fn log_header_area_size() -> (out: u64) 
        requires 
            LogMetadata::spec_size_of() * 2 <= u64::MAX,
            u64::spec_size_of() + LogMetadata::spec_size_of() * 2 <= u64::MAX,
            u64::spec_size_of() + LogMetadata::spec_size_of() * 2 + u64::spec_size_of() * 2 <= u64::MAX
        ensures 
            out == spec_log_header_area_size()
    {
        (size_of::<u64>() + size_of::<LogMetadata>() * 2 + size_of::<u64>() * 2) as u64
    }

    pub open spec fn spec_log_area_pos() -> nat {
        256
    }

    #[inline]
    pub fn log_area_pos() -> (out: u64) 
        ensures out == spec_log_area_pos()
    {
        256
    }

    pub open spec fn spec_log_header_pos_cdb_false() -> nat {
        u64::spec_size_of()
    }

    pub exec fn log_header_pos_cdb_false() -> (out: u64) 
        ensures 
            out == spec_log_header_pos_cdb_false()
    {
        size_of::<u64>() as u64
    }

    pub open spec fn spec_log_header_pos_cdb_true() -> nat
    {
        u64::spec_size_of() + LogMetadata::spec_size_of() + u64::spec_size_of()
    }

    pub exec fn log_header_pos_cdb_true() -> (out: u64) 
        ensures 
            out == spec_log_header_pos_cdb_true()
    {
        proof { reveal(spec_padding_needed); }
        (size_of::<u64>() + size_of::<LogMetadata>() + size_of::<u64>()) as u64
    }

    pub open spec fn spec_get_log_cdb(mem: Seq<u8>, log_start_addr: nat) -> u64
    {
        let bytes = extract_bytes(mem, log_start_addr, u64::spec_size_of());
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn spec_check_log_cdb(mem: Seq<u8>, log_start_addr: nat) -> Option<bool>
    {
        let cdb = spec_get_log_cdb(mem, log_start_addr);
        if cdb == CDB_TRUE {
            Some(true)
        } else if cdb == CDB_FALSE {
            Some(false)
        } else {
            None
        }
    }

    pub open spec fn spec_get_active_log_metadata_pos(cdb: bool) -> nat {
        if cdb { spec_log_header_pos_cdb_true() } else { spec_log_header_pos_cdb_false() }
    }

    pub exec fn get_active_log_metadata_pos(cdb: bool) -> (out: u64)
        ensures
            out == spec_get_active_log_metadata_pos(cdb),
    {
        if cdb {
            log_header_pos_cdb_true()
        }
        else {
            log_header_pos_cdb_false()
        }
    }

    pub open spec fn spec_get_inactive_log_metadata_pos(cdb: bool) -> nat 
    {
        if !cdb { spec_log_header_pos_cdb_true() } else { spec_log_header_pos_cdb_false() }
    }

    pub exec fn get_inactive_log_metadata_pos(cdb: bool) -> (out: u64) 
        ensures 
            out == spec_get_inactive_log_metadata_pos(cdb)
    {
        if !cdb {
            log_header_pos_cdb_true()
        }
        else {
            log_header_pos_cdb_false()
        }
    }

    pub open spec fn spec_get_inactive_log_metadata(mem: Seq<u8>, log_start_addr: nat, cdb: bool) -> LogMetadata 
    {
        let pos = spec_get_inactive_log_metadata_pos(cdb) + log_start_addr;
        let bytes = extract_bytes(mem, pos, LogMetadata::spec_size_of());
        LogMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn spec_get_active_log_metadata(mem: Seq<u8>, log_start_addr: nat, cdb: bool) -> LogMetadata 
    {
        let pos = spec_get_active_log_metadata_pos(cdb) + log_start_addr;
        let bytes = extract_bytes(mem, pos, LogMetadata::spec_size_of());
        LogMetadata::spec_from_bytes(bytes)
    }

    pub open spec fn spec_get_active_log_crc_pos(cdb: bool) -> nat
    {
        if cdb { 
            spec_log_header_pos_cdb_true() + LogMetadata::spec_size_of()
        } else { 
            spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()
        }
    }

    pub open spec fn spec_get_inactive_log_crc_pos(cdb: bool) -> nat
    {
        if !cdb { 
            spec_log_header_pos_cdb_true() + LogMetadata::spec_size_of()
        } else { 
            spec_log_header_pos_cdb_false() + LogMetadata::spec_size_of()
        }
    }

    pub open spec fn spec_get_active_log_crc(mem: Seq<u8>, log_start_addr: nat, cdb: bool) -> u64
    {
        let pos = spec_get_active_log_crc_pos(cdb) + log_start_addr;
        let bytes = extract_bytes(mem, pos, u64::spec_size_of());
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn spec_get_inactive_log_crc(mem: Seq<u8>, log_start_addr: nat, cdb: bool) -> u64
    {
        let pos = spec_get_inactive_log_crc_pos(cdb) + log_start_addr;
        let bytes = extract_bytes(mem, pos, u64::spec_size_of());
        u64::spec_from_bytes(bytes)
    }

    pub open spec fn spec_get_active_log_crc_end(cdb: bool) -> nat
    {
        spec_get_active_log_crc_pos(cdb) + u64::spec_size_of()
    }

    pub exec fn get_active_log_crc_pos(cdb: bool) -> (out: u64)
        ensures
            out == spec_get_active_log_crc_pos(cdb)
    {
        proof { reveal(spec_padding_needed); }
        if cdb { 
            log_header_pos_cdb_true() + size_of::<LogMetadata>() as u64
        } else { 
            log_header_pos_cdb_false() + size_of::<LogMetadata>() as u64
        }
    }

    // This function converts a virtual log position (given relative
    // to the virtual log's head) to a memory location (given relative
    // to the beginning of the log area in memory).
    //
    // `pos_relative_to_head` -- the position in the virtual log being
    // asked about, expressed as the number of positions past the
    // virtual head (e.g., if the head is 3 and this is 7, it
    // means position 10 in the virtual log).
    //
    // `head_log_area_offset` -- the offset from the location in the
    // log area in memory containing the head position of the virtual
    // log (e.g., if this is 3, that means the log's head byte is at
    // address ABSOLUTE_POS_OF_LOG_AREA + 3 in the persistent memory
    // region)
    //
    // `log_area_len` -- the length of the log area in memory
    pub open spec fn relative_log_pos_to_log_area_offset(
        pos_relative_to_head: int,
        head_log_area_offset: int,
        log_area_len: int
    ) -> int
    {
        let log_area_offset = head_log_area_offset + pos_relative_to_head;
        if log_area_offset >= log_area_len {
            log_area_offset - log_area_len
        }
        else {
            log_area_offset
        }
    }

    pub open spec fn log_area_offset_to_relative_log_pos(
        log_area_offset: int,
        head_log_area_offset: int,
        log_area_len: int
    ) -> int
    {
        if log_area_offset >= head_log_area_offset {
            log_area_offset - head_log_area_offset
        }
        else {
            log_area_offset - head_log_area_offset + log_area_len
        }
    }

    // This function extracts the virtual log from the contents of a
    // persistent-memory region.
    //
    // `mem` -- the contents of the persistent-memory region
    //
    // `log_area_len` -- the size of the log area in that region
    //
    // `head` -- the virtual log position of the head
    //
    // `log_length` -- the current length of the virtual log past the
    // head
    pub open spec fn extract_log_from_log_area(log_area: Seq<u8>, head: int, log_length: int) -> Seq<u8>
    {
        let head_log_area_offset = head % (log_area.len() as int);
        Seq::<u8>::new(log_length as nat, |pos_relative_to_head: int|
                       log_area[relative_log_pos_to_log_area_offset(pos_relative_to_head, head_log_area_offset,
                                                                    log_area.len() as int)])
    }

    // `mem` should be the subrange of bytes that comprise the log
    pub open spec fn recover_state(mem: Seq<u8>, log_start_addr: nat, log_size: nat) -> Option<AbstractLogState>
    {
        match recover_cdb(mem, log_start_addr) {
            Some(cdb) => recover_given_cdb(mem, log_start_addr, log_size, cdb),
            None => None
        }
    }

    pub open spec fn recover_cdb(mem: Seq<u8>, log_start_addr: nat) -> Option<bool> 
    {
        if mem.len() < u64::spec_size_of() {
            None 
        } else {
            let cdb = spec_get_log_cdb(mem, log_start_addr);
            if cdb == CDB_FALSE {
                Some(false)
            } else if cdb == CDB_TRUE {
                Some(true)
            } else {
                None
            }
        }
    }

    pub open spec fn recover_given_cdb(mem: Seq<u8>, log_start_addr: nat, log_size: nat, cdb: bool)
                                       -> Option<AbstractLogState>
    {
        if mem.len() < log_start_addr + spec_log_area_pos() + MIN_LOG_AREA_SIZE {
            None 
        } else {
            let metadata = spec_get_active_log_metadata(mem, log_start_addr, cdb);
            let crc = spec_get_active_log_crc(mem, log_start_addr, cdb);
            if crc != metadata.spec_crc() {
                None
            } else {
                recover_log(mem, log_start_addr, log_size, metadata.head as int, metadata.log_length as int)
            }
        }
    }

    pub open spec fn recover_log(mem: Seq<u8>, log_start_addr: nat, log_size: nat, head: int, len: int)
                                 -> Option<AbstractLogState>
    {
        if mem.len() < log_start_addr + log_size {
            None
        }
        else if log_size - spec_log_area_pos() < len || head + len > u128::MAX {
            None 
        } else {
            let log_area = extract_bytes(mem, log_start_addr + spec_log_area_pos(),
                                         (log_size - spec_log_area_pos()) as nat);
            Some(AbstractLogState {
                head,
                log: extract_log_from_log_area(log_area, head, len),
                pending: Seq::<u8>::empty(),
                capacity: log_size - spec_log_area_pos(),
            })
        }
    }
}
