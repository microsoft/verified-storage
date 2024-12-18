use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use crate::common::align_v::*;
use crate::common::saturate_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

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
    pub journal_static_metadata_start: u64,
    pub journal_static_metadata_end: u64,
    pub journal_static_metadata_crc_start: u64,
    pub journal_dynamic_area_start: u64,
    pub program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

#[repr(C)]
#[derive(PmCopy, Copy, Default, Debug)]
pub struct JournalStaticMetadata {
    pub app_version_number: u64,
    pub committed_cdb_start: u64,
    pub journal_length_start: u64,
    pub journal_length_crc_start: u64,
    pub journal_data_start: u64,
    pub journal_data_end: u64,
    pub app_static_area_start: u64,
    pub app_static_area_end: u64,
    pub app_dynamic_area_start: u64,
    pub app_dynamic_area_end: u64,
    pub app_program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

pub struct JournalEntry
{
    pub addr: int,
    pub bytes: Seq<u8>,
}

pub open spec fn validate_version_metadata(m: JournalVersionMetadata) -> bool
{
    &&& m.version_number == JOURNAL_PROGRAM_VERSION_NUMBER
    &&& m.program_guid == JOURNAL_PROGRAM_GUID
    &&& JournalVersionMetadata::spec_size_of() + u64::spec_size_of() <= m.journal_static_metadata_start
    &&& opaque_aligned(m.journal_static_metadata_start as int, JournalStaticMetadata::spec_align_of() as int)
    &&& m.journal_static_metadata_start + JournalStaticMetadata::spec_size_of() <= m.journal_static_metadata_end
    &&& m.journal_static_metadata_end <= m.journal_static_metadata_crc_start
    &&& opaque_aligned(m.journal_static_metadata_crc_start as int, u64::spec_size_of() as int)
    &&& m.journal_static_metadata_crc_start <= m.journal_dynamic_area_start
}

pub open spec fn recover_version_metadata(bytes: Seq<u8>) -> Option<JournalVersionMetadata>
{
    let crc_start = round_up_to_alignment(JournalVersionMetadata::spec_size_of() as int, u64::spec_align_of() as int);
    match recover_object::<JournalVersionMetadata>(bytes, 0, crc_start) {
        Some(m) => if validate_version_metadata(m) { Some(m) } else { None },
        None => None,
    }
}

pub open spec fn validate_static_metadata(m: JournalStaticMetadata, journal_dynamic_area_start: int,
                                          len: nat) -> bool
{
    &&& journal_dynamic_area_start <= m.committed_cdb_start
    &&& m.committed_cdb_start + u64::spec_size_of() <= m.journal_length_start
    &&& opaque_aligned(m.committed_cdb_start as int, const_persistence_chunk_size() as int)
    &&& m.journal_length_start + u64::spec_size_of() <= m.journal_length_crc_start
    &&& m.journal_length_crc_start + u64::spec_size_of() <= m.journal_data_start
    &&& m.journal_data_start <= m.journal_data_end
    &&& m.journal_data_end <= m.app_static_area_start
    &&& m.app_static_area_start <= m.app_static_area_end
    &&& m.app_static_area_end <= m.app_dynamic_area_start
    &&& m.app_dynamic_area_start <= m.app_dynamic_area_end
    &&& m.app_dynamic_area_end <= len
}

pub open spec fn recover_static_metadata(bytes: Seq<u8>, start: int, crc_start: int, dynamic_area_start: int)
                                         -> Option<JournalStaticMetadata>
{
    match recover_object::<JournalStaticMetadata>(bytes, start, crc_start) {
        Some(m) => if validate_static_metadata(m, dynamic_area_start, bytes.len()) { Some(m) } else { None },
        None => None,
    }
}

pub open spec fn recover_app_static_area(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    if sm.app_static_area_start <= sm.app_static_area_end && sm.app_static_area_end <= bytes.len() {
        Some(opaque_subrange(bytes, sm.app_static_area_start as int, sm.app_static_area_end as int))
    }
    else {
        None
    }
}

pub open spec fn recover_journal_data(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    match recover_object::<u64>(bytes, sm.journal_length_start as int, sm.journal_length_crc_start as int) {
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
        &&& 0 <= sm.app_dynamic_area_start <= entry.addr
        &&& entry.addr + bytes.len() <= sm.app_dynamic_area_end
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

pub open spec fn recover_journal_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
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
                            let app_bytes = opaque_subrange(updated_bytes, sm.app_dynamic_area_start as int,
                                                            sm.app_dynamic_area_end as int);
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
            match recover_static_metadata(bytes, version_metadata.journal_static_metadata_start as int,
                                          version_metadata.journal_static_metadata_crc_start as int,
                                          version_metadata.journal_dynamic_area_start as int) {
                None => None,
                Some(sm) => {
                    match recover_cdb(bytes, sm.committed_cdb_start as int) {
                        None => None,
                        Some(committed) => {
                            if committed {
                                recover_journal_case_committed(bytes, sm)
                            }
                            else {
                                Some(opaque_subrange(bytes, sm.app_dynamic_area_start as int, sm.app_dynamic_area_end as int))
                            }
                        },
                    }
                },
            }
        },
    }
}

}
