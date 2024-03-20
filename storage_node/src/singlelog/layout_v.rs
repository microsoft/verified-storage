//! This file describes the persistent-memory layout used by the
//! singlelog implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//! Each persistent-memory region used to store a log will have the following layout.
//!
//! Level-1 metadata:  Metadata whose length is constant across all versions
//! Level-2 metadata:  Metadata that never changes over the course of execution
//! Level-3 metadata:  Metadata that changes as the data changes, so it
//!                    has two versions and a corruption-detecting boolean
//!                    distinguishing which of those two versions is active
//! Log area:          Area where log is written
//!
//! Only the first region's corruption-detecting boolean is used, and
//! it dictates which level-3 metadata is used on *all* regions. The
//! corruption-detecting boolean on all other regions is ignored.
//!
//! Level-1 metadata (absolute offsets):
//!   bytes 0..16:    Program GUID for this program
//!   bytes 16..24:   Version number of the program that created this metadata
//!   bytes 24..32:   Length of level-2 metadata, not including CRC (i.e., 60 + length of singlelog ID)
//!   bytes 32..40:   CRC of the above 32 bytes
//!
//! Level-2 metadata (absolute offsets):
//!   bytes 40..48:   This region's size
//!   bytes 48..64:   Multilog ID
//!   bytes 64..68:   Number of logs in the singlelog
//!   bytes 68..72:   Index of this log in the multlog (0 = first)
//!   bytes 72..80:   Length of log area (LoLA)
//!   bytes 80..88:   CRC of the above 40 bytes
//!
//! Level-3 metadata (relative offsets):
//!   bytes 0..16:    Log head virtual position
//!   bytes 16..24:   Log length
//!   bytes 24..32:   CRC of the above 24 bytes
//!
//! Log area (relative offsets):
//!   bytes 0..LoLA:   Byte #n is the one whose virtual log position modulo LoLA is n
//!
//! The way the corruption-detecting boolean (CDB) detects corruption
//! is as follows. To write a CDB to persistent memory, we store one
//! of two eight-byte values: `CDB_FALSE` or `CDB_TRUE`. These are
//! sufficiently different from one another that each is extremely
//! unlikely to be corrupted to become the other. So, if corruption
//! happens, we can detect it by the fact that something other than
//! `CDB_FALSE` or `CDB_TRUE` was read.
//!

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::singlelog::singlelogspec_t::AbstractLogState;
use builtin::*;
use builtin_macros::*;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    /// Constants

    // These constants describe the absolute or relative positions of
    // various parts of the layout.

    pub const ABSOLUTE_POS_OF_LEVEL1_METADATA: u64 = 0;
    pub const RELATIVE_POS_OF_LEVEL1_PROGRAM_GUID: u64 = 0;
    pub const RELATIVE_POS_OF_LEVEL1_VERSION_NUMBER: u64 = 16;
    pub const RELATIVE_POS_OF_LEVEL1_LENGTH_OF_LEVEL2_METADATA: u64 = 24;
    pub const LENGTH_OF_LEVEL1_METADATA: u64 = 32;
    pub const ABSOLUTE_POS_OF_LEVEL1_CRC: u64 = 32;
    pub const ABSOLUTE_POS_OF_LEVEL2_METADATA: u64 = 40;
    pub const RELATIVE_POS_OF_LEVEL2_REGION_SIZE: u64 = 0;
    pub const RELATIVE_POS_OF_LEVEL2_MULTILOG_ID: u64 = 8;
    pub const RELATIVE_POS_OF_LEVEL2_NUM_LOGS: u64 = 24;
    pub const RELATIVE_POS_OF_LEVEL2_WHICH_LOG: u64 = 28;
    pub const RELATIVE_POS_OF_LEVEL2_LENGTH_OF_LOG_AREA: u64 = 32;
    pub const LENGTH_OF_LEVEL2_METADATA: u64 = 40;
    pub const ABSOLUTE_POS_OF_LEVEL2_CRC: u64 = 80;
    pub const ABSOLUTE_POS_OF_LEVEL3_CDB: u64 = 88;
    pub const ABSOLUTE_POS_OF_LEVEL3_METADATA_FOR_CDB_FALSE: u64 = 96;
    pub const ABSOLUTE_POS_OF_LEVEL3_METADATA_FOR_CDB_TRUE: u64 = 128;
    pub const RELATIVE_POS_OF_LEVEL3_HEAD: u64 = 0;
    pub const RELATIVE_POS_OF_LEVEL3_LOG_LENGTH: u64 = 16;
    pub const LENGTH_OF_LEVEL3_METADATA: u64 = 24;
    pub const ABSOLUTE_POS_OF_LEVEL3_CRC_FOR_CDB_FALSE: u64 = 120;
    pub const ABSOLUTE_POS_OF_LEVEL3_CRC_FOR_CDB_TRUE: u64 = 152;
    pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 160;
    pub const MIN_LOG_AREA_SIZE: u64 = 1;

    // This GUID was generated randomly and is meant to describe the
    // singlelog program, even if it has future versions.

    pub const MULTILOG_PROGRAM_GUID: u128 = 0x21b8b4b3c7d140a9abf7e80c07b7f01fu128;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const MULTILOG_PROGRAM_VERSION_NUMBER: u64 = 1;

    // These structs represent the different levels of metadata.

    pub struct Level1Metadata {
        pub program_guid: u128,
        pub version_number: u64,
        pub length_of_level2_metadata: u64,
    }

    pub struct Level2Metadata {
        pub region_size: u64,
        pub log_id: u128,
        pub num_logs: u32,
        pub which_log: u32,
        pub log_area_len: u64,
    }

    pub struct Level3Metadata {
        pub head: u128,
        pub log_length: u64,
    }

    /// Specification functions for extracting metadata from a
    /// persistent-memory region.

    // This function extracts the subsequence of `bytes` that lie
    // between `pos` and `pos + len` inclusive of `pos` but exclusive
    // of `pos + len`.
    pub open spec fn extract_bytes(bytes: Seq<u8>, pos: int, len: int) -> Seq<u8>
    {
        bytes.subrange(pos, pos + len)
    }

    // This function extracts the bytes encoding level-1 metadata from
    // the contents `mem` of a persistent memory region.
    pub open spec fn extract_level1_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL1_METADATA as int, LENGTH_OF_LEVEL1_METADATA as int)
    }

    // This function extracts the CRC of the level-1 metadata from the
    // contents `mem` of a persistent memory region.
    pub open spec fn extract_level1_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL1_CRC as int, CRC_SIZE as int)
    }

    // This function extracts the bytes encoding level-2 metadata
    // from the contents `mem` of a persistent memory region.
    pub open spec fn extract_level2_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL2_METADATA as int, LENGTH_OF_LEVEL2_METADATA as int)
    }

    // This function extracts the CRC of the level-2 metadata from the
    // contents `mem` of a persistent memory region.
    pub open spec fn extract_level2_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL2_CRC as int, CRC_SIZE as int)
    }

    // This function extracts the bytes encoding the level-3
    // corruption-detecting boolean (i.e., CDB) from the contents
    // `mem` of a persistent memory region.
    pub open spec fn extract_level3_cdb(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LEVEL3_CDB as int, CRC_SIZE as int)
    }

    // This function extracts the level-3 corruption-detecting boolean
    // (i.e., CDB) from the contents `mem` of a persistent memory
    // region. It returns an Option<bool> with the following meanings:
    //
    // None -- Corruption was detected when reading the CDB
    // Some(true) -- No corruption was detected and the CDB is true
    // Some(false) -- No corruption was detected and the CDB is false
    //
    // pub open spec fn extract_and_parse_level3_cdb(mem: Seq<u8>) -> Option<bool>
    // {
    //     let level3_cdb = extract_level3_cdb(mem);
    //     if spec_u64_from_le_bytes(level3_cdb) == CDB_FALSE {
    //         Some(false)
    //     }
    //     else if spec_u64_from_le_bytes(level3_cdb) == CDB_TRUE {
    //         Some(true)
    //     }
    //     else {
    //         None
    //     }
    // }
    pub open spec fn parse_cdb(mem: Seq<u8>) -> Option<bool>
    {
        if mem.len() != 8 {
            None
        } else if spec_u64_from_le_bytes(mem) == CDB_FALSE {
            Some(false)
        } else if spec_u64_from_le_bytes(mem) == CDB_TRUE {
            Some(true)
        } else {
            None
        }
    }

    // This function computes where the level-3 metadata will be in a
    // persistent-memory region given the current boolean value `cdb`
    // of the corruption-detecting boolean.
    pub open spec fn get_level3_metadata_pos(cdb: bool) -> u64
    {
        if cdb { ABSOLUTE_POS_OF_LEVEL3_METADATA_FOR_CDB_TRUE } else { ABSOLUTE_POS_OF_LEVEL3_METADATA_FOR_CDB_FALSE }
    }

    // This function computes where the level-3 metadata ends in a
    // persistent-memory region (i.e., the index of the byte just past
    // the end of the level-3 metadata) given the current boolean
    // value `cdb` of the corruption-detecting boolean.
    pub open spec fn get_level3_crc_end(cdb: bool) -> u64
    {
        (get_level3_metadata_pos(cdb) + LENGTH_OF_LEVEL3_METADATA + CRC_SIZE) as u64
    }

    // This function extracts the bytes encoding level-3 metadata from
    // the contents `mem` of a persistent memory region. It needs to
    // know the current boolean value `cdb` of the
    // corruption-detecting boolean because there are two possible
    // places for such metadata.
    pub open spec fn extract_level3_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = get_level3_metadata_pos(cdb);
        extract_bytes(mem, pos as int, LENGTH_OF_LEVEL3_METADATA as int)
    }

    // This function extracts the CRC of the level-3 metadata from the
    // contents `mem` of a persistent memory region. It needs to know
    // the current boolean value `cdb` of the corruption-detecting
    // boolean because there are two possible places for that CRC.
    pub open spec fn extract_level3_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = if cdb { ABSOLUTE_POS_OF_LEVEL3_CRC_FOR_CDB_TRUE }
                  else { ABSOLUTE_POS_OF_LEVEL3_CRC_FOR_CDB_FALSE };
        extract_bytes(mem, pos as int, CRC_SIZE as int)
    }

    // This function returns the 4-byte unsigned integer (i.e., u32)
    // encoded at position `pos` in byte sequence `bytes`.
    pub open spec fn parse_u32(bytes: Seq<u8>, pos: int) -> u32
    {
        spec_u32_from_le_bytes(extract_bytes(bytes, pos, 4))
    }

    // This function returns the 8-byte unsigned integer (i.e., u64)
    // encoded at position `pos` in byte sequence `bytes`.
    pub open spec fn parse_u64(bytes: Seq<u8>, pos: int) -> u64
    {
        spec_u64_from_le_bytes(extract_bytes(bytes, pos, 8))
    }

    // This function returns the 16-byte unsigned integer (i.e., u128)
    // encoded at position `pos` in byte sequence `bytes`.
    pub open spec fn parse_u128(bytes: Seq<u8>, pos: int) -> u128
    {
        spec_u128_from_le_bytes(extract_bytes(bytes, pos, 16))
    }

    // This function returns the level-1 metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_level1_metadata(bytes: Seq<u8>) -> Level1Metadata
    {
        let program_guid = parse_u128(bytes, RELATIVE_POS_OF_LEVEL1_PROGRAM_GUID as int);
        let version_number = parse_u64(bytes, RELATIVE_POS_OF_LEVEL1_VERSION_NUMBER as int);
        let length_of_level2_metadata = parse_u64(bytes, RELATIVE_POS_OF_LEVEL1_LENGTH_OF_LEVEL2_METADATA as int);
        Level1Metadata { program_guid, version_number, length_of_level2_metadata }
    }

    // This function returns the level-2 metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_level2_metadata(bytes: Seq<u8>) -> Level2Metadata
    {
        let region_size = parse_u64(bytes, RELATIVE_POS_OF_LEVEL2_REGION_SIZE as int);
        let log_id = parse_u128(bytes, RELATIVE_POS_OF_LEVEL2_MULTILOG_ID as int);
        let num_logs = parse_u32(bytes, RELATIVE_POS_OF_LEVEL2_NUM_LOGS as int);
        let which_log = parse_u32(bytes, RELATIVE_POS_OF_LEVEL2_WHICH_LOG as int);
        let log_area_len = parse_u64(bytes, RELATIVE_POS_OF_LEVEL2_LENGTH_OF_LOG_AREA as int);
        Level2Metadata { region_size, log_id, num_logs, which_log, log_area_len }
    }

    // This function returns the level-3 metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_level3_metadata(bytes: Seq<u8>) -> Level3Metadata
    {
        let head = parse_u128(bytes, RELATIVE_POS_OF_LEVEL3_HEAD as int);
        let log_length = parse_u64(bytes, RELATIVE_POS_OF_LEVEL3_LOG_LENGTH as int);
        Level3Metadata { head, log_length }
    }

    /// Specification functions for extracting log data from a
    /// persistent-memory region.

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
    pub open spec fn extract_log(mem: Seq<u8>, log_area_len: int, head: int, log_length: int) -> Seq<u8>
    {
        let head_log_area_offset = head % log_area_len;
        Seq::<u8>::new(log_length as nat, |pos_relative_to_head: int| mem[ABSOLUTE_POS_OF_LOG_AREA +
            relative_log_pos_to_log_area_offset(pos_relative_to_head, head_log_area_offset, log_area_len)])
    }

    /// Specification functions for recovering data and metadata from
    /// persistent memory after a crash

    // This function specifies how recovery should treat the contents
    // of a single persistent-memory region as an abstract log state.
    // It only deals with data; it assumes the metadata has already
    // been recovered. Relevant aspects of that metadata are passed in
    // as parameters.
    //
    // `mem` -- the contents of the persistent-memory region
    //
    // `log_area_len` -- the size of the log area in that region
    //
    // `head` -- the virtual log position of the head
    //
    // `log_length` -- the current length of the virtual log past the
    // head
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the given metadata isn't valid
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_abstract_log_from_region_given_metadata(
        mem: Seq<u8>,
        log_area_len: u64,
        head: u128,
        log_length: u64,
    ) -> Option<AbstractLogState>
    {
        if log_length > log_area_len || head + log_length > u128::MAX
        {
            None
        }
        else {
            Some(AbstractLogState {
                head: head as int,
                log: extract_log(mem, log_area_len as int, head as int, log_length as int),
                pending: Seq::<u8>::empty(),
                capacity: log_area_len as int
            })
        }
    }

    // This function specifies how recovery should treat the contents
    // of a single persistent-memory region as an abstract log state.
    // It assumes the corruption-detecting boolean has already been
    // read and is given by `cdb`.
    //
    // `mem` -- the contents of the persistent-memory region
    //
    // `log_id` -- the GUID associated with the singlelog when it
    // was initialized
    //
    // `num_logs` -- the number of logs overall in the singlelog that
    // this region's log is part of
    //
    // `which_log` -- which log, among the logs in the singlelog,
    // that this region stores
    //
    // `cdb` -- what value the corruption-detecting boolean has,
    // according to the metadata in region 0
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the metadata on persistent memory isn't consistent
    // with it having been used as a singlelog with the given
    // parameters
    //
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_abstract_log_from_region_given_cdb(
        mem: Seq<u8>,
        log_id: u128,
        num_logs: int,
        which_log: int,
        cdb: bool
    ) -> Option<AbstractLogState>
    {
        if mem.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            // To be valid, the memory's length has to be big enough to store at least
            // `MIN_LOG_AREA_SIZE` in the log area.
            None
        }
        else {
            let level1_metadata_bytes = extract_level1_metadata(mem);
            let level1_crc = extract_level1_crc(mem);
            if level1_crc != spec_crc_bytes(level1_metadata_bytes) {
                // To be valid, the level-1 CRC has to be a valid CRC of the level-1 metadata
                // encoded as bytes.
                None
            }
            else {
                let level1_metadata = parse_level1_metadata(level1_metadata_bytes);
                if level1_metadata.program_guid != MULTILOG_PROGRAM_GUID {
                    // To be valid, the level-1 metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if level1_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if level1_metadata.length_of_level2_metadata != LENGTH_OF_LEVEL2_METADATA {
                        // To be valid, the level-1 metadata's encoding of the level-2 metadata's
                        // length has to be what we expect. (This version of the code doesn't
                        // support any other length of level-2 metadata.)
                        None
                    }
                    else {
                        let level2_metadata_bytes = extract_level2_metadata(mem);
                        let level2_crc = extract_level2_crc(mem);
                        if level2_crc != spec_crc_bytes(level2_metadata_bytes) {
                            // To be valid, the level-2 CRC has to be a valid CRC of the level-2
                            // metadata encoded as bytes.
                            None
                        }
                        else {
                            let level2_metadata = parse_level2_metadata(level2_metadata_bytes);
                            // To be valid, the level-2 region size has to match the size of the
                            // region given to us. Also, its metadata has to match what we expect
                            // from the list of regions given to us. Finally, there has to be
                            // sufficient room for the log area.
                            if {
                                ||| level2_metadata.region_size != mem.len()
                                ||| level2_metadata.log_id != log_id
                                ||| level2_metadata.num_logs != num_logs
                                ||| level2_metadata.which_log != which_log
                                ||| level2_metadata.log_area_len < MIN_LOG_AREA_SIZE
                                ||| mem.len() < ABSOLUTE_POS_OF_LOG_AREA + level2_metadata.log_area_len
                            } {
                                None
                            }
                            else {
                                let level3_metadata_bytes = extract_level3_metadata(mem, cdb);
                                let level3_crc = extract_level3_crc(mem, cdb);
                                if level3_crc != spec_crc_bytes(level3_metadata_bytes) {
                                    // To be valid, the level-3 CRC has to be a valid CRC of the
                                    // level-3 metadata encoded as bytes. (This only applies to the
                                    // "active" level-3 metadata, i.e., the level-3 metadata
                                    // corresponding to the current CDB.)
                                    None
                                }
                                else {
                                    let level3_metadata = parse_level3_metadata(level3_metadata_bytes);
                                    recover_abstract_log_from_region_given_metadata(
                                        mem, level2_metadata.log_area_len, level3_metadata.head,
                                        level3_metadata.log_length)
                                }
                            }
                        }
                    }
                }
                else {
                    // This version of the code doesn't know how to parse metadata for any other
                    // versions of this code besides 1. If we reach this point, we're presumably
                    // reading metadata written by a future version of this code, which we can't
                    // interpret.
                    None
                }
            }
        }
    }

    // This function specifies how recovery should treat the contents
    // of a sequence of persistent memory regions as an abstract
    // singlelog state. It assumes the corruption-detecting boolean has
    // already been read and is given by `cdb`.
    //
    // `mems` -- the contents of the sequence of persistent memory
    // regions, i.e., a sequence of sequences of bytes, with one
    // sequence of bytes per persistent-memory region
    //
    // `log_id` -- the GUID associated with the singlelog when it
    // was initialized
    //
    // `cdb` -- what value the corruption-detecting boolean has,
    // according to the metadata in region 0
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the metadata on persistent memory isn't consistent
    // with it having been used as a singlelog with the given
    // parameters
    //
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_given_cdb(
        mems: Seq<Seq<u8>>,
        log_id: u128,
        cdb: bool
    ) -> Option<AbstractLogState>
    {
        // For each region, use `recover_abstract_log_from_region_given_cdb` to recover it.  One of
        // the parameters to that function is `which_log`, which we fill in with the index of the
        // memory region within the sequence `mems`.
        let seq_option = mems.map(|idx, c| recover_abstract_log_from_region_given_cdb(c, log_id, mems.len() as int,
                                                                                      idx, cdb));

        // If any of those recoveries failed, fail this recovery. Otherwise, amass all the recovered
        // `AbstractLogState` values into a sequence to construct an `AbstractLogState`.
        if forall |i| 0 <= i < seq_option.len() ==> seq_option[i].is_Some() {
            Some(AbstractLogState{ states: seq_option.map(|_idx, ot: Option<AbstractLogState>| ot.unwrap()) })
        }
        else {
            None
        }
    }

    // This function specifies how recovery should recover the
    // corruption-detecting boolean. The input `mem` is the contents
    // of region #0 of the persistent memory regions, since the CDB is
    // only stored there.
    //
    // Returns an `Option<bool>` with the following meaning:
    //
    // `None` -- the metadata on this region isn't consistent
    // with it having been used as a singlelog
    //
    // `Some(cdb)` -- `cdb` is the corruption-detecting boolean
    pub open spec fn recover_cdb(mem: Seq<u8>) -> Option<bool>
    {
        if mem.len() < ABSOLUTE_POS_OF_LEVEL2_METADATA {
            // If there isn't space in memory to store the level-1 metadata
            // and CRC, then this region clearly isn't a valid singlelog
            // region #0.
            None
        }
        else {
            let level1_metadata_bytes = extract_level1_metadata(mem);
            let level1_crc = extract_level1_crc(mem);
            if level1_crc != spec_crc_bytes(level1_metadata_bytes) {
                // To be valid, the level-1 CRC has to be a valid CRC of the level-1 metadata
                // encoded as bytes.
                None
            }
            else {
                let level1_metadata = parse_level1_metadata(level1_metadata_bytes);
                if level1_metadata.program_guid != MULTILOG_PROGRAM_GUID {
                    // To be valid, the level-1 metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if level1_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if mem.len() < ABSOLUTE_POS_OF_LEVEL3_CDB + CRC_SIZE {
                        // If memory isn't big enough to store the CDB, then this region isn't
                        // valid.
                        None
                    }
                    else {
                        // Extract and parse the level-3 CDB
                        extract_and_parse_level3_cdb(mem)
                    }
                }
                else {
                    // This version of the code doesn't know how to parse metadata for any other
                    // versions of this code besides 1. If we reach this point, we're presumably
                    // reading metadata written by a future version of this code, which we can't
                    // interpret.
                    None
                }
            }
        }
    }

    // This function specifies how recovery should treat the contents
    // of a sequence of persistent-memory regions as an abstract
    // singlelog state.
    //
    // `mems` -- the contents of the persistent memory regions, i.e.,
    // a sequence of sequences of bytes, with one sequence of bytes
    // per persistent-memory region
    //
    // `log_id` -- the GUID associated with the singlelog when it
    // was initialized
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the metadata on persistent memory isn't consistent
    // with it having been used as a singlelog with the given singlelog
    // ID
    //
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_all(mems: Seq<Seq<u8>>, log_id: u128) -> Option<AbstractLogState>
    {
        if mems.len() < 1 || mems.len() > u32::MAX {
            // There needs to be at least one region for it to be
            // valid, and there can't be more regions than can fit in
            // a u32.
            None
        }
        else {
            // To recover, first recover the CDB from region #0, then
            // use it to recover the abstract state from all the
            // regions (including region #0).
            match recover_cdb(mems[0]) {
                Some(cdb) => recover_given_cdb(mems, log_id, cdb),
                None => None
            }
        }
    }

    /// Useful utility proofs about layout that other files use.

    // This lemma establishes that if a persistent memory regions view
    // `pm_regions_view` has no outstanding writes, and if its committed byte
    // sequence recovers to abstract state `state`, then any state
    // `pm_regions_view` can crash into also recovers that same abstract state.
    pub proof fn lemma_if_no_outstanding_writes_then_can_only_crash_as_state(
        pm_regions_view: PersistentMemoryRegionsView,
        log_id: u128,
        state: AbstractLogState,
    )
        requires
            pm_regions_view.no_outstanding_writes(),
            recover_all(pm_regions_view.committed(), log_id) == Some(state),
        ensures
            forall |s| #[trigger] pm_regions_view.can_crash_as(s) ==> recover_all(s, log_id) == Some(state)
    {
        // This follows trivially from the observation that the only
        // byte sequence `pm_regions_view` can crash into is its committed byte
        // sequence. (It has no outstanding writes, so there's nothing
        // else it could crash into.)
        lemma_if_no_outstanding_writes_then_persistent_memory_regions_view_can_only_crash_as_committed(pm_regions_view);
    }

    // This lemma establishes that if persistent memory regions'
    // contents `mems` can successfully be recovered from, then each
    // of its regions has size large enough to hold at least
    // `MIN_LOG_AREA_SIZE` bytes in its log area.
    pub proof fn lemma_recover_all_successful_implies_region_sizes_sufficient(mems: Seq<Seq<u8>>, log_id: u128)
        requires
            recover_all(mems, log_id).is_Some()
        ensures
            forall |i| 0 <= i < mems.len() ==> #[trigger] mems[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
    {
        assert forall |i| 0 <= i < mems.len() implies
                   #[trigger] mems[i].len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE by
        {
            let cdb = recover_cdb(mems[0]).get_Some_0();
            let recovered_mems = mems.map(|idx, c| recover_abstract_log_from_region_given_cdb(
                c, log_id, mems.len() as int, idx, cdb));
            // We have to mention `recovered_mems[i]` to trigger the `forall` in `recover_given_cdb`
            // and thereby learn that it's Some. Everything we need follows easily from that.
            assert(recovered_mems[i].is_Some());
        }
    }

    // This lemma establishes that for any `i` and `n`, if
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // holds, then
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    //
    // also holds.
    //
    // This is an obvious fact, so the body of the lemma is
    // empty. Nevertheless, the lemma is useful because it establishes
    // a trigger. Specifically, it hints Z3 that whenever Z3 is
    // thinking about two terms `extract_bytes(mem1, i, n)` and
    // `extract_bytes(mem2, i, n)` where `mem1` and `mem2` are the
    // specific memory byte sequences passed to this lemma, Z3 should
    // also think about this lemma's conclusion. That is, it should
    // try to prove that
    //
    // `forall |k| 0 <= k < n ==> mem1[i+k] == mem2[i+k]`
    //
    // and, whenever it can prove that, conclude that
    //
    // `extract_bytes(mem1, i, n) == mem2.extract_bytes(mem2, i, n)`
    pub proof fn lemma_establish_extract_bytes_equivalence(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    )
        ensures
            forall |i: int, n: int| extract_bytes(mem1, i, n) =~= extract_bytes(mem2, i, n) ==>
                #[trigger] extract_bytes(mem1, i, n) == #[trigger] extract_bytes(mem2, i, n)
    {
    }

    // This lemma establishes that if the given persistent memory
    // regions' contents can be recovered to a valid abstract state,
    // then that abstract state is unaffected by
    // `drop_pending_appends`.
    pub proof fn lemma_recovered_state_is_crash_idempotent(mems: Seq<Seq<u8>>, log_id: u128)
        requires
            recover_all(mems, log_id).is_Some()
        ensures
            ({
                let state = recover_all(mems, log_id).unwrap();
                state == state.drop_pending_appends()
            })
    {
        let state = recover_all(mems, log_id).unwrap();
        assert forall |which_log: int| #![trigger state[which_log]] 0 <= which_log < state.num_logs()
            implies state[which_log].pending.len() == 0 by {
        }
        assert(state =~= state.drop_pending_appends());
    }
}
