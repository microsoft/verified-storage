use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::util_v::*;
use deps_hack::{PmCopy};

verus! {

    pub const APP_AREA_ALIGNMENT: u64 = 16;

    pub const ABSOLUTE_POS_OF_VERSION_METADATA: u64 = 0;

    // This GUID was generated randomly and is meant to describe the
    // journal module, even if it has future versions.

    pub const JOURNAL_PROGRAM_GUID: u128 = 0xf41bb8dd3ccc4a77bb76c8f3a5319d6a;

    // The current version number, and the only one whose contents
    // this program can read, is the following:

    pub const JOURNAL_PROGRAM_VERSION_NUMBER: u64 = 1;

    #[repr(C)]
    #[derive(PmCopy, Copy, Default)]
    pub struct JournalVersionMetadata {
        pub version_number: u64,
        pub static_metadata_addr: u64,
        pub program_guid: u128,
    }

    #[repr(C)]
    #[derive(PmCopy, Copy, Default, Debug)]
    pub struct JournalStaticMetadata {
        pub committed_cdb_addr: u64,
        pub journal_length_addr: u64,
        pub journal_data_start: u64,
        pub journal_data_end: u64,
        pub app_area_start: u64,
        pub app_area_end: u64,
    }

    pub struct JournalEntry
    {
        pub addr: int,
        pub bytes: Seq<u8>,
    }

    pub open spec fn validate_version_metadata(m: JournalVersionMetadata) -> bool
    {
        &&& m.version_number == JOURNAL_PROGRAM_VERSION_NUMBER
        &&& JournalVersionMetadata::spec_size_of() <= m.static_metadata_addr
        &&& m.program_guid == JOURNAL_PROGRAM_GUID
    }

    pub open spec fn recover_version_metadata(bytes: Seq<u8>) -> Option<JournalVersionMetadata>
    {
        match recover_object::<JournalVersionMetadata>(bytes, 0) {
            Some(m) => if validate_version_metadata(m) { Some(m) } else { None },
            None => None,
        }

    }

    pub open spec fn validate_static_metadata(m: JournalStaticMetadata, addr: int, len: nat) -> bool
    {
        &&& addr + JournalStaticMetadata::spec_size_of() <= m.committed_cdb_addr
        &&& m.committed_cdb_addr + u64::spec_size_of() <= m.journal_length_addr
        &&& m.journal_length_addr + u64::spec_size_of() + u64::spec_size_of() <= m.journal_data_start
        &&& m.journal_data_start + u64::spec_size_of() <= m.journal_data_end
        &&& m.journal_data_end <= m.app_area_start <= m.app_area_end <= len
        &&& opaque_aligned(m.committed_cdb_addr as int, const_persistence_chunk_size() as int)
        &&& opaque_aligned(m.app_area_start as int, APP_AREA_ALIGNMENT as int)
    }

    pub open spec fn recover_static_metadata(bytes: Seq<u8>, addr: int) -> Option<JournalStaticMetadata>
    {
        match recover_object::<JournalStaticMetadata>(bytes, addr) {
            Some(m) => if validate_static_metadata(m, addr, bytes.len()) { Some(m) } else { None },
            None => None,
        }
    }

    pub open spec fn recover_journal_data(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
    {
        match recover_object::<u64>(bytes, sm.journal_length_addr as int) {
            None => None,
            Some(journal_length) => {
                if {
                    &&& 0 <= sm.journal_data_start
                    &&& sm.journal_data_start + journal_length + u64::spec_size_of() <= sm.journal_data_end
                    &&& sm.journal_data_end <= bytes.len()
                } {
                    let journal_data = opaque_section(bytes, sm.journal_data_start as int, journal_length as nat);
                    let journal_data_crc = opaque_section(bytes, sm.journal_data_start + journal_length,
                                                          u64::spec_size_of());
                    if journal_data_crc == spec_crc_bytes(journal_data) {
                        Some(journal_data)
                    }
                    else {
                        None
                    }
                }
                else {
                    None
                }
            },
        }
    }

    pub open spec fn parse_journal_data(journal_data: Seq<u8>, start: int) -> Option<Seq<JournalEntry>>
        decreases
            journal_data.len() - start
    {
        if !(0 <= start <= journal_data.len()) {
            None
        }
        else if journal_data.len() == start {
            Some(Seq::<JournalEntry>::empty())
        }
        else if start + u64::spec_size_of() + u64::spec_size_of() > journal_data.len() {
            None
        }
        else {
            let addr_bytes = opaque_section(journal_data, start, u64::spec_size_of());
            let addr = u64::spec_from_bytes(addr_bytes);
            let length_offset = start + u64::spec_size_of();
            let length_bytes = opaque_section(journal_data, length_offset, u64::spec_size_of());
            let length = u64::spec_from_bytes(length_bytes);
            let data_offset = length_offset + u64::spec_size_of();
            if data_offset + length > journal_data.len() {
                None
            }
            else {
                let data = opaque_section(journal_data, data_offset, length as nat);
                let entry = JournalEntry { addr: addr as int, bytes: data };
                match parse_journal_data(journal_data, data_offset + length) {
                    None => None,
                    Some(remaining_journal) => Some(seq![entry] + remaining_journal),
                }
            }
        }
    }

    pub open spec fn apply_journal_entry(bytes: Seq<u8>, entry: JournalEntry, sm: JournalStaticMetadata)
                                         -> Option<Seq<u8>>
    {
        if {
            &&& 0 <= sm.app_area_start <= entry.addr
            &&& entry.addr + bytes.len() <= sm.app_area_end
        } {
            Some(opaque_update_bytes(bytes, entry.addr, entry.bytes))
        }
        else {
            None
        }
    }

    pub open spec fn apply_journal_entries(bytes: Seq<u8>, entries: Seq<JournalEntry>, starting_entry: int,
                                           sm: JournalStaticMetadata) -> Option<Seq<u8>>
        decreases
            entries.len() - starting_entry
    {
        if starting_entry < 0 || starting_entry > entries.len() {
            None
        }
        else if entries.len() == starting_entry {
            Some(bytes)
        }
        else {
            match apply_journal_entry(bytes, entries[starting_entry], sm) {
                None => None,
                Some(updated_bytes) => apply_journal_entries(updated_bytes, entries, starting_entry + 1, sm),
            }
        }
    }

    pub closed spec fn recover_journal_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
    {
        match recover_journal_data(bytes, sm) {
            None => None,
            Some(journal_data) => {
                match parse_journal_data(journal_data, 0) {
                    None => None,
                    Some(journal_entries) => {
                        match apply_journal_entries(bytes, journal_entries, 0, sm) {
                            None => None,
                            Some(updated_bytes) => {
                                let app_bytes = opaque_subrange(updated_bytes, sm.app_area_start as int,
                                                                sm.app_area_end as int);
                                Some(app_bytes)
                            },
                        }
                    },
                }
            },
        }
    }

    #[verifier::opaque]
    pub open spec fn recover_journal(bytes: Seq<u8>) -> Option<Seq<u8>>
    {
        match recover_version_metadata(bytes) {
            None => None,
            Some(version_metadata) => {
                match recover_static_metadata(bytes, version_metadata.static_metadata_addr as int) {
                    None => None,
                    Some(sm) => {
                        match recover_cdb(bytes, sm.committed_cdb_addr as int) {
                            None => None,
                            Some(committed) => {
                                if committed {
                                    recover_journal_case_committed(bytes, sm)
                                }
                                else {
                                    Some(opaque_subrange(bytes, sm.app_area_start as int, sm.app_area_end as int))
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}
