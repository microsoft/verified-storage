//! This file describes the persistent-memory layout used by the
//! log implementation.
//!
//! The code in this file is verified and untrusted (as indicated by
//! the `_v.rs` suffix), so you don't have to read it to be confident
//! of the system's correctness.
//!
//! The persistent-memory region used to store a log will have the following layout.
//!
//! Global metadata:   Metadata whose length is constant across all versions and
//!                    the same for each region/log
//! Region metadata:   Metadata that does not change over the course of
//!                    execution.
//! Log metadata:      Metadata that changes as the data changes, so it
//!                    has two versions and a corruption-detecting boolean
//!                    distinguishing which of those two versions is active
//! Log area:          Area where log is written
//!
//! The corruption-detecting boolean dictates which of the two instances of
//! log metadata is used.
//!
//! Global metadata (absolute offsets):
//!   bytes 0..8:     Version number of the program that created this metadata
//!   bytes 8..16:    Length of region metadata, not including CRC
//!   bytes 16..32:   Program GUID for this program  
//!   bytes 32..40:   CRC of the above 32 bytes
//!
//! Region metadata (absolute offsets):
//!   bytes 40..48:   This region's size
//!   bytes 48..56:   Length of log area (LoLA)
//!   bytes 56..72:   Log ID
//!   bytes 72..80:   CRC of the above 32 bytes
//!
//! Log metadata (relative offsets):
//!   bytes 0..8:     Log length
//!   bytes 8..16:    Unused padding bytes
//!   bytes 16..32:   Log head virtual position
//!   bytes 32..40:   CRC of the above 32 bytes
//!
//! Log area (relative offsets):
//!   bytes 0..LoLA:   Byte #n is the one whose virtual log position modulo LoLA is n
//!
//! The log area starts at absolute offset 256 to improve Intel Optane DC PMM performance.
//!
//! The way the corruption-detecting boolean (CDB) detects corruption
//! is as follows. To write a CDB to persistent memory, we store one
//! of two eight-byte values: `CDB_FALSE` or `CDB_TRUE`. These are
//! sufficiently different from one another that each is extremely
//! unlikely to be corrupted to become the other. So, if corruption
//! happens, we can detect it by the fact that something other than
//! `CDB_FALSE` or `CDB_TRUE` was read.
//!

use crate::log::logspec_t::AbstractLogState;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use core::fmt::Debug;
use vstd::bytes::*;
use vstd::prelude::*;

verus! {

    /// Constants

    // These constants describe the absolute or relative positions of
    // various parts of the layout.

    pub const ABSOLUTE_POS_OF_GLOBAL_METADATA: u64 = 0;
    pub const RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER: u64 = 0;
    pub const RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA: u64 = 8;
    pub const RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID: u64 = 16;
    pub const LENGTH_OF_GLOBAL_METADATA: u64 = 32;
    pub const ABSOLUTE_POS_OF_GLOBAL_CRC: u64 = 32;

    pub const ABSOLUTE_POS_OF_REGION_METADATA: u64 = 40;
    pub const RELATIVE_POS_OF_REGION_REGION_SIZE: u64 = 0;
    pub const RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA: u64 = 8;
    pub const RELATIVE_POS_OF_REGION_LOG_ID: u64 = 16;
    pub const LENGTH_OF_REGION_METADATA: u64 = 32;
    pub const ABSOLUTE_POS_OF_REGION_CRC: u64 = 72;

    pub const ABSOLUTE_POS_OF_LOG_CDB: u64 = 80;
    pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE: u64 = 88;
    pub const ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE: u64 = 128;
    pub const RELATIVE_POS_OF_LOG_LOG_LENGTH: u64 = 0;
    pub const RELATIVE_POS_OF_LOG_PADDING: u64 = 8;
    pub const RELATIVE_POS_OF_LOG_HEAD: u64 = 16;
    pub const LENGTH_OF_LOG_METADATA: u64 = 32;
    pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE: u64 = 120;
    pub const ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE: u64 = 160;
    pub const ABSOLUTE_POS_OF_LOG_AREA: u64 = 256;
    pub const MIN_LOG_AREA_SIZE: u64 = 1;

    // This GUID was generated randomly and is meant to describe the
    // multilog program, even if it has future versions.

    pub const LOG_PROGRAM_GUID: u128 = 0x8eecd9dea2de4443903e2acf951380bf;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const LOG_PROGRAM_VERSION_NUMBER: u64 = 1;

    // These structs represent the different levels of metadata.
    // TODO: confirm with runtime checks that the sizes and offsets are as expected

    #[repr(C)]
    pub struct GlobalMetadata {
        pub version_number: u64,
        pub length_of_region_metadata: u64,
        pub program_guid: u128,
    }

    impl Serializable for GlobalMetadata {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.version_number) +
                spec_u64_to_le_bytes(self.length_of_region_metadata) +
                spec_u128_to_le_bytes(self.program_guid)

        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                version_number: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER as int, RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER + 8)),
                length_of_region_metadata: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA as int, RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA + 8)),
                program_guid: spec_u128_from_le_bytes(bytes.subrange(
                    RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID as int, RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_guid = #[trigger] spec_u128_to_le_bytes(s.program_guid);
                let serialized_version = #[trigger] spec_u64_to_le_bytes(s.version_number);
                let serialized_region_len = #[trigger] spec_u64_to_le_bytes(s.length_of_region_metadata);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER as int,
                        RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER + 8
                    ) == serialized_version
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA as int,
                        RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA + 8
                    ) == serialized_region_len
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID as int,
                        RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID + 16
                    ) == serialized_guid
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        open spec fn spec_serialized_len() -> int {
            LENGTH_OF_GLOBAL_METADATA as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_GLOBAL_METADATA
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }

    #[repr(C)]
    pub struct RegionMetadata {
        pub region_size: u64,
        pub log_area_len: u64,
        pub log_id: u128,
    }

    impl Serializable for RegionMetadata {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.region_size) + spec_u64_to_le_bytes(self.log_area_len) +
                spec_u128_to_le_bytes(self.log_id)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                region_size: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_REGION_REGION_SIZE as int, RELATIVE_POS_OF_REGION_REGION_SIZE + 8)),
                log_area_len: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA as int, RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA + 8)),
                log_id: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_REGION_LOG_ID as int, RELATIVE_POS_OF_REGION_LOG_ID + 16)),
            }
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_region_size = #[trigger] spec_u64_to_le_bytes(s.region_size);
                let serialized_len = #[trigger] spec_u64_to_le_bytes(s.log_area_len);
                let serialized_id = #[trigger] spec_u128_to_le_bytes(s.log_id);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_REGION_REGION_SIZE as int,
                        RELATIVE_POS_OF_REGION_REGION_SIZE + 8
                    ) == serialized_region_size
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA as int,
                        RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA + 8
                    ) == serialized_len
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_REGION_LOG_ID as int,
                        RELATIVE_POS_OF_REGION_LOG_ID + 16
                    ) == serialized_id
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u32_to_from_le_bytes();
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        open spec fn spec_serialized_len() -> int
        {
            LENGTH_OF_REGION_METADATA as int
        }

        fn serialized_len() -> u64
        {
            LENGTH_OF_REGION_METADATA
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
    }

    #[repr(C)]
    pub struct LogMetadata {
        pub log_length: u64,
        pub _padding: u64,
        pub head: u128,
    }

    impl Serializable for LogMetadata {
        open spec fn spec_serialize(self) -> Seq<u8>
        {
            spec_u64_to_le_bytes(self.log_length) + spec_u64_to_le_bytes(self._padding) + spec_u128_to_le_bytes(self.head)
        }

        open spec fn spec_deserialize(bytes: Seq<u8>) -> Self
        {
            Self {
                log_length: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_LOG_LENGTH as int, RELATIVE_POS_OF_LOG_LOG_LENGTH + 8)),
                _padding: spec_u64_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_PADDING as int, RELATIVE_POS_OF_LOG_PADDING + 8)),
                head: spec_u128_from_le_bytes(
                    bytes.subrange(RELATIVE_POS_OF_LOG_HEAD as int, RELATIVE_POS_OF_LOG_HEAD + 16)),
            }
        }

        open spec fn spec_serialized_len() -> int
        {
            LENGTH_OF_LOG_METADATA as int
        }

        proof fn lemma_auto_serialize_deserialize()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |s: Self| {
                let serialized_log_length = #[trigger] spec_u64_to_le_bytes(s.log_length);
                let serialized_padding = #[trigger] spec_u64_to_le_bytes(s._padding);
                let serialized_head = #[trigger] spec_u128_to_le_bytes(s.head);
                let serialized_metadata = #[trigger] s.spec_serialize();
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LOG_LOG_LENGTH as int,
                        RELATIVE_POS_OF_LOG_LOG_LENGTH + 8,
                    ) == serialized_log_length
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LOG_PADDING as int,
                        RELATIVE_POS_OF_LOG_PADDING + 8
                    ) == serialized_padding
                &&& serialized_metadata.subrange(
                        RELATIVE_POS_OF_LOG_HEAD as int,
                        RELATIVE_POS_OF_LOG_HEAD + 16
                    ) == serialized_head
            });
        }

        proof fn lemma_auto_deserialize_serialize() {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
            assert(forall |bytes: Seq<u8>| #![auto] bytes.len() == Self::spec_serialized_len() ==>
                bytes =~= Self::spec_deserialize(bytes).spec_serialize());
        }

        proof fn lemma_auto_serialized_len()
        {
            lemma_auto_spec_u64_to_from_le_bytes();
            lemma_auto_spec_u128_to_from_le_bytes();
        }

        fn serialized_len() -> u64 {
            LENGTH_OF_LOG_METADATA
        }

        #[verifier::external_body]
        exec fn deserialize_bytes(bytes: &[u8]) -> (out: &Self) 
        {
            let ptr = bytes.as_ptr() as *const Self;
            unsafe { &*ptr }
        }
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

    // This function extracts the bytes encoding global metadata from
    // the contents `mem` of a persistent memory region.
    pub open spec fn extract_global_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_METADATA as int, LENGTH_OF_GLOBAL_METADATA as int)
    }

    pub open spec fn deserialize_global_metadata(mem: Seq<u8>) -> GlobalMetadata
    {
        let bytes = extract_global_metadata(mem);
        GlobalMetadata::spec_deserialize(bytes)
    }

    // This function extracts the CRC of the global metadata from the
    // contents `mem` of a persistent memory region.
    pub open spec fn extract_global_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_GLOBAL_CRC as int, CRC_SIZE as int)
    }

    pub open spec fn deserialize_global_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_global_crc(mem);
        u64::spec_deserialize(bytes)
    }

    // This function extracts the bytes encoding region metadata
    // from the contents `mem` of a persistent memory region.
    pub open spec fn extract_region_metadata(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_METADATA as int, LENGTH_OF_REGION_METADATA as int)
    }

    pub open spec fn deserialize_region_metadata(mem: Seq<u8>) -> RegionMetadata
    {
        let bytes = extract_region_metadata(mem);
        RegionMetadata::spec_deserialize(bytes)
    }

    // This function extracts the CRC of the region metadata from the
    // contents `mem` of a persistent memory region.
    pub open spec fn extract_region_crc(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_REGION_CRC as int, CRC_SIZE as int)
    }

    pub open spec fn deserialize_region_crc(mem: Seq<u8>) -> u64
    {
        let bytes = extract_region_crc(mem);
        u64::spec_deserialize(bytes)
    }

    // This function extracts the bytes encoding the log metadata's
    // corruption-detecting boolean (i.e., CDB) from the contents
    // `mem` of a persistent memory region.
    pub open spec fn extract_log_cdb(mem: Seq<u8>) -> Seq<u8>
    {
        extract_bytes(mem, ABSOLUTE_POS_OF_LOG_CDB as int, CRC_SIZE as int)
    }

    // This function extracts the log metadata's corruption-detecting boolean
    // (i.e., CDB) from the contents `mem` of a persistent memory
    // region. It returns an Option<bool> with the following meanings:
    //
    // None -- Corruption was detected when reading the CDB
    // Some(true) -- No corruption was detected and the CDB is true
    // Some(false) -- No corruption was detected and the CDB is false
    //
    pub open spec fn extract_and_parse_log_cdb(mem: Seq<u8>) -> Option<bool>
    {
        let log_cdb = extract_log_cdb(mem);
        if spec_u64_from_le_bytes(log_cdb) == CDB_FALSE {
            Some(false)
        }
        else if spec_u64_from_le_bytes(log_cdb) == CDB_TRUE {
            Some(true)
        }
        else {
            None
        }
    }

    pub open spec fn deserialize_log_cdb(mem: Seq<u8>) -> u64
    {
        let bytes = extract_log_cdb(mem);
        u64::spec_deserialize(bytes)
    }

    pub open spec fn deserialize_and_check_log_cdb(mem: Seq<u8>) -> Option<bool>
    {
        let log_cdb = deserialize_log_cdb(mem);
        if log_cdb == CDB_FALSE {
            Some(false)
        } else if log_cdb == CDB_TRUE {
            Some(true)
        } else {
            None
        }
    }

    // This function computes where the log metadata will be in a
    // persistent-memory region given the current boolean value `cdb`
    // of the corruption-detecting boolean.
    pub open spec fn get_log_metadata_pos(cdb: bool) -> u64
    {
        if cdb { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_TRUE } else { ABSOLUTE_POS_OF_LOG_METADATA_FOR_CDB_FALSE }
    }

    // This function computes where the log metadata ends in a
    // persistent-memory region (i.e., the index of the byte just past
    // the end of the log metadata) given the current boolean
    // value `cdb` of the corruption-detecting boolean.
    pub open spec fn get_log_crc_end(cdb: bool) -> u64
    {
        (get_log_metadata_pos(cdb) + LENGTH_OF_LOG_METADATA + CRC_SIZE) as u64
    }

    // This function extracts the bytes encoding log metadata from
    // the contents `mem` of a persistent memory region. It needs to
    // know the current boolean value `cdb` of the
    // corruption-detecting boolean because there are two possible
    // places for such metadata.
    pub open spec fn extract_log_metadata(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = get_log_metadata_pos(cdb);
        extract_bytes(mem, pos as int, LENGTH_OF_LOG_METADATA as int)
    }

    pub open spec fn deserialize_log_metadata(mem: Seq<u8>, cdb: bool) -> LogMetadata
    {
        let bytes = extract_log_metadata(mem, cdb);
        LogMetadata::spec_deserialize(bytes)
    }

    // This function extracts the CRC of the log metadata from the
    // contents `mem` of a persistent memory region. It needs to know
    // the current boolean value `cdb` of the corruption-detecting
    // boolean because there are two possible places for that CRC.
    pub open spec fn extract_log_crc(mem: Seq<u8>, cdb: bool) -> Seq<u8>
    {
        let pos = if cdb { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_TRUE }
                  else { ABSOLUTE_POS_OF_LOG_CRC_FOR_CDB_FALSE };
        extract_bytes(mem, pos as int, CRC_SIZE as int)
    }

    pub open spec fn deserialize_log_crc(mem: Seq<u8>, cdb: bool) -> u64
    {
        let bytes = extract_log_crc(mem, cdb);
        u64::spec_deserialize(bytes)
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

    // This function returns the global metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_global_metadata(bytes: Seq<u8>) -> GlobalMetadata
    {
        let program_guid = parse_u128(bytes, RELATIVE_POS_OF_GLOBAL_PROGRAM_GUID as int);
        let version_number = parse_u64(bytes, RELATIVE_POS_OF_GLOBAL_VERSION_NUMBER as int);
        let length_of_region_metadata = parse_u64(bytes, RELATIVE_POS_OF_GLOBAL_LENGTH_OF_REGION_METADATA as int);
        GlobalMetadata { program_guid, version_number, length_of_region_metadata }
    }

    // This function returns the region metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_region_metadata(bytes: Seq<u8>) -> RegionMetadata
    {
        let region_size = parse_u64(bytes, RELATIVE_POS_OF_REGION_REGION_SIZE as int);
        let log_id = parse_u128(bytes, RELATIVE_POS_OF_REGION_LOG_ID as int);
        let log_area_len = parse_u64(bytes, RELATIVE_POS_OF_REGION_LENGTH_OF_LOG_AREA as int);
        RegionMetadata { region_size, log_id, log_area_len }
    }

    // This function returns the log metadata encoded as the given
    // bytes `bytes`.
    pub open spec fn parse_log_metadata(bytes: Seq<u8>) -> LogMetadata
    {
        let head = parse_u128(bytes, RELATIVE_POS_OF_LOG_HEAD as int);
        let log_length = parse_u64(bytes, RELATIVE_POS_OF_LOG_LOG_LENGTH as int);
        LogMetadata { head, _padding: 0, log_length }
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
    // of the persistent-memory region as an abstract log state.
    // It assumes the corruption-detecting boolean has already been
    // read and is given by `cdb`.
    //
    // `mem` -- the contents of the persistent-memory region
    //
    // `log_id` -- the GUID associated with the log when it
    // was initialized
    //
    // `cdb` -- what value the corruption-detecting boolean has,
    // according to the metadata in region 0
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the metadata on persistent memory isn't consistent
    // with it having been used as a multilog with the given
    // parameters
    //
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_given_cdb(
        mem: Seq<u8>,
        log_id: u128,
        cdb: bool
    ) -> Option<AbstractLogState>
    {
        if mem.len() < ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE {
            // To be valid, the memory's length has to be big enough to store at least
            // `MIN_LOG_AREA_SIZE` in the log area.
            None
        }
        else {
            let global_metadata = deserialize_global_metadata(mem);
            let global_crc = deserialize_global_crc(mem);
            if global_crc != global_metadata.spec_crc() {
                // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
                // encoded as bytes.
                None
            }
            else {
                if global_metadata.program_guid != LOG_PROGRAM_GUID {
                    // To be valid, the global metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if global_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if global_metadata.length_of_region_metadata != LENGTH_OF_REGION_METADATA {
                        // To be valid, the global metadata's encoding of the region metadata's
                        // length has to be what we expect. (This version of the code doesn't
                        // support any other length of region metadata.)
                        None
                    }
                    else {
                        let region_metadata = deserialize_region_metadata(mem);
                        let region_crc = deserialize_region_crc(mem);
                        if region_crc != region_metadata.spec_crc() {
                            // To be valid, the region metadata CRC has to be a valid CRC of the region
                            // metadata encoded as bytes.
                            None
                        }
                        else {
                            // To be valid, the region metadata's region size has to match the size of the
                            // region given to us. Also, its metadata has to match what we expect
                            // from the list of regions given to us. Finally, there has to be
                            // sufficient room for the log area.
                            if {
                                ||| region_metadata.region_size != mem.len()
                                ||| region_metadata.log_id != log_id
                                ||| region_metadata.log_area_len < MIN_LOG_AREA_SIZE
                                ||| mem.len() < ABSOLUTE_POS_OF_LOG_AREA + region_metadata.log_area_len
                            } {
                                None
                            }
                            else {
                                let log_metadata = deserialize_log_metadata(mem, cdb);
                                let log_crc = deserialize_log_crc(mem, cdb);
                                if log_crc != log_metadata.spec_crc() {
                                    // To be valid, the log metadata CRC has to be a valid CRC of the
                                    // log metadata encoded as bytes. (This only applies to the
                                    // "active" log metadata, i.e., the log metadata
                                    // corresponding to the current CDB.)
                                    None
                                }
                                else {
                                    recover_abstract_log_from_region_given_metadata(
                                        mem, region_metadata.log_area_len, log_metadata.head,
                                        log_metadata.log_length)
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

    // This function specifies how recovery should recover the
    // corruption-detecting boolean. The input `mem` is the contents
    // of the persistent memory region.
    //
    // Returns an `Option<bool>` with the following meaning:
    //
    // `None` -- the metadata on this region isn't consistent
    // with it having been used as a log
    //
    // `Some(cdb)` -- `cdb` is the corruption-detecting boolean
    pub open spec fn recover_cdb(mem: Seq<u8>) -> Option<bool>
    {
        if mem.len() < ABSOLUTE_POS_OF_REGION_METADATA {
            // If there isn't space in memory to store the global metadata
            // and CRC, then this region clearly isn't a valid log region.
            None
        }
        else {
            let global_metadata = deserialize_global_metadata(mem);
            let global_crc = deserialize_global_crc(mem);
            if global_crc != global_metadata.spec_crc() {
                // To be valid, the global metadata CRC has to be a valid CRC of the global metadata
                // encoded as bytes.
                None
            }
            else {
                if global_metadata.program_guid != LOG_PROGRAM_GUID {
                    // To be valid, the global metadata has to refer to this program's GUID.
                    // Otherwise, it wasn't created by this program.
                    None
                }
                else if global_metadata.version_number == 1 {
                    // If this metadata was written by version #1 of this code, then this is how to
                    // interpret it:

                    if mem.len() < ABSOLUTE_POS_OF_LOG_CDB + CRC_SIZE {
                        // If memory isn't big enough to store the CDB, then this region isn't
                        // valid.
                        None
                    }
                    else {
                        // Extract and parse the log metadata CDB
                        deserialize_and_check_log_cdb(mem)
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
    // of a persistent-memory region as an abstract log state.
    //
    // `mem` -- the contents of the persistent memory region
    //
    // `log_id` -- the GUID associated with the log when it
    // was initialized
    //
    // Returns an `Option<AbstractLogState>` with the following
    // meaning:
    //
    // `None` -- the metadata on persistent memory isn't consistent
    // with it having been used as a log with the given log ID
    //
    // `Some(s)` -- `s` is the abstract state represented in memory
    pub open spec fn recover_state(mem: Seq<u8>, log_id: u128) -> Option<AbstractLogState>
    {
        // To recover, first recover the CDB, then use it to recover the abstract state.
        match recover_cdb(mem) {
            Some(cdb) => recover_given_cdb(mem, log_id, cdb),
            None => None
        }
    }

    /// Useful utility proofs about layout that other files use.

    // This lemma establishes that if a persistent memory region view
    // `pm_region_view` has no outstanding writes, and if its committed byte
    // sequence recovers to abstract state `state`, then any state
    // `pm_region_view` can crash into also recovers that same abstract state.
    pub proof fn lemma_if_no_outstanding_writes_then_can_only_crash_as_state(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    )
        requires
            pm_region_view.no_outstanding_writes(),
            recover_state(pm_region_view.committed(), log_id) == Some(state),
        ensures
            forall |s| #[trigger] pm_region_view.can_crash_as(s) ==> recover_state(s, log_id) == Some(state)
    {
        // This follows trivially from the observation that the only
        // byte sequence `pm_region_view` can crash into is its committed byte
        // sequence. (It has no outstanding writes, so there's nothing
        // else it could crash into.)
        lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(pm_region_view);
    }

    // This lemma establishes that if a persistent memory region's
    // contents `mem` can successfully be recovered from, then it has
    // size large enough to hold at least `MIN_LOG_AREA_SIZE` bytes in
    // its log area.
    pub proof fn lemma_recover_state_successful_implies_region_size_sufficient(mem: Seq<u8>, log_id: u128)
        requires
            recover_state(mem, log_id).is_Some()
        ensures
            mem.len() >= ABSOLUTE_POS_OF_LOG_AREA + MIN_LOG_AREA_SIZE
    {
        let cdb = recover_cdb(mem).get_Some_0();
        let recovered_mem = recover_given_cdb(mem, log_id, cdb);
        assert(recovered_mem.is_Some());
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

    pub proof fn lemma_same_bytes_same_deserialization<S>(mem1: Seq<u8>, mem2: Seq<u8>)
        where
            S: Serializable + Sized
        ensures
            forall |i: int, n: int| extract_bytes(mem1, i, n) =~= extract_bytes(mem2, i, n) ==>
                S::spec_deserialize(#[trigger] extract_bytes(mem1, i, n)) == S::spec_deserialize(#[trigger] extract_bytes(mem2, i, n))
    {}

    // This lemma establishes that if the given persistent memory
    // region's contents can be recovered to a valid abstract state,
    // then that abstract state is unaffected by
    // `drop_pending_appends`.
    pub proof fn lemma_recovered_state_is_crash_idempotent(mem: Seq<u8>, log_id: u128)
        requires
            recover_state(mem, log_id).is_Some()
        ensures
            ({
                let state = recover_state(mem, log_id).unwrap();
                state == state.drop_pending_appends()
            })
    {
        let state = recover_state(mem, log_id).unwrap();
        assert(state.pending.len() == 0);
        assert(state =~= state.drop_pending_appends());
    }
}
