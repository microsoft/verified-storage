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
use super::entry_v::*;
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
#[verifier::ext_equal]
pub struct JournalVersionMetadata {
    pub version_number: u64,
    pub program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

#[repr(C)]
#[derive(PmCopy, Copy, Default, Debug)]
#[verifier::ext_equal]
pub(super) struct JournalStaticMetadata {
    pub(super) app_version_number: u64,
    pub(super) committed_cdb_start: u64,
    pub(super) journal_length_start: u64,
    pub(super) journal_length_crc_start: u64,
    pub(super) journal_entries_crc_start: u64,
    pub(super) journal_entries_start: u64,
    pub(super) journal_entries_end: u64,
    pub(super) app_area_start: u64,
    pub(super) app_area_end: u64,
    pub(super) app_program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

pub(super) open spec fn spec_journal_version_metadata_start() -> int
{
    0
}

pub(super) open spec fn spec_journal_version_metadata_end() -> int
{
    JournalVersionMetadata::spec_size_of() as int
}

pub(super) open spec fn spec_journal_version_metadata_crc_start() -> int
{
    round_up_to_alignment(spec_journal_version_metadata_end(), u64::spec_align_of() as int)
}

pub(super) open spec fn spec_journal_version_metadata_crc_end() -> int
{
    spec_journal_version_metadata_crc_start() + u64::spec_size_of() as int
}

pub(super) open spec fn spec_journal_static_metadata_start() -> int
{
    round_up_to_alignment(spec_journal_version_metadata_crc_end(), JournalStaticMetadata::spec_align_of() as int)
}

pub(super) open spec fn spec_journal_static_metadata_end() -> int
{
    spec_journal_static_metadata_start() + JournalStaticMetadata::spec_size_of()
}

pub(super) open spec fn spec_journal_static_metadata_crc_start() -> int
{
    round_up_to_alignment(spec_journal_static_metadata_end(), u64::spec_align_of() as int)
}

pub(super) open spec fn spec_journal_static_metadata_crc_end() -> int
{
    spec_journal_static_metadata_crc_start() + u64::spec_size_of() as int
}

pub(super) open spec fn validate_version_metadata(m: JournalVersionMetadata) -> bool
{
    &&& spec_journal_version_metadata_end() <= spec_journal_version_metadata_crc_start()
    &&& m.program_guid == JOURNAL_PROGRAM_GUID
}

pub(super) open spec fn recover_version_metadata(bytes: Seq<u8>) -> Option<JournalVersionMetadata>
{
    if spec_journal_version_metadata_crc_end() > bytes.len() {
        None
    }
    else {
        match recover_object::<JournalVersionMetadata>(bytes, spec_journal_version_metadata_start(),
                                                       spec_journal_version_metadata_crc_start()) {
            Some(vm) => if validate_version_metadata(vm) { Some(vm) } else { None },
            None => None,
        }
    }
}

pub(super) open spec fn validate_static_metadata(sm: JournalStaticMetadata, vm: JournalVersionMetadata) -> bool
{
    if vm.version_number == JOURNAL_PROGRAM_VERSION_NUMBER {
        &&& spec_journal_version_metadata_crc_end() <= spec_journal_static_metadata_start()
        &&& spec_journal_static_metadata_start() + JournalStaticMetadata::spec_size_of()
               <= spec_journal_static_metadata_end()
        &&& spec_journal_static_metadata_end() <= spec_journal_static_metadata_crc_start()
        &&& spec_journal_static_metadata_crc_start() + u64::spec_size_of() == spec_journal_static_metadata_crc_end()
        &&& spec_journal_static_metadata_crc_end() <= sm.committed_cdb_start
        &&& sm.committed_cdb_start + u64::spec_size_of() <= sm.journal_length_start
        &&& opaque_aligned(sm.committed_cdb_start as int, const_persistence_chunk_size() as int)
        &&& sm.journal_length_start + u64::spec_size_of() <= sm.journal_length_crc_start
        &&& sm.journal_length_crc_start + u64::spec_size_of() <= sm.journal_entries_crc_start
        &&& sm.journal_entries_crc_start + u64::spec_size_of() <= sm.journal_entries_start
        &&& sm.journal_entries_start <= sm.journal_entries_end
        &&& sm.journal_entries_end <= sm.app_area_start
        &&& sm.app_area_start <= sm.app_area_end
    }
    else {
        false
    }
}

pub(super) open spec fn recover_static_metadata(bytes: Seq<u8>, vm: JournalVersionMetadata)
                                         -> Option<JournalStaticMetadata>
{
    if spec_journal_static_metadata_crc_end() > bytes.len() {
        None
    }
    else {
        match recover_object::<JournalStaticMetadata>(bytes, spec_journal_static_metadata_start(),
                                                      spec_journal_static_metadata_crc_start()) {
            Some(sm) => if validate_static_metadata(sm, vm) && sm.app_area_end == bytes.len() {
                Some(sm)
            } else {
                None
            },
            None => None,
        }
    }
}

pub(super) open spec fn validate_metadata(vm: JournalVersionMetadata, sm: JournalStaticMetadata, num_bytes: nat) -> bool
{
    &&& validate_version_metadata(vm)
    &&& validate_static_metadata(sm, vm)
    &&& spec_journal_version_metadata_crc_end() <= num_bytes
    &&& spec_journal_static_metadata_crc_end() <= num_bytes
    &&& sm.app_area_end == num_bytes
}

pub(super) open spec fn recover_journal_length(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<u64>
{
    recover_object::<u64>(bytes, sm.journal_length_start as int, sm.journal_length_crc_start as int)
}

pub(super) open spec fn recover_journal_entries_bytes(bytes: Seq<u8>, sm: JournalStaticMetadata, journal_length: u64)
    -> Option<Seq<u8>>
{
    if {
        &&& 0 <= sm.journal_entries_start
        &&& sm.journal_entries_start + journal_length <= sm.journal_entries_end
        &&& sm.journal_entries_end <= bytes.len()
        &&& 0 <= sm.journal_entries_crc_start
        &&& sm.journal_entries_crc_start + u64::spec_size_of() <= bytes.len()
    } {
        let journal_entries = opaque_section(bytes, sm.journal_entries_start as int, journal_length as nat);
        let journal_entries_crc_bytes = opaque_section(bytes, sm.journal_entries_crc_start as int, u64::spec_size_of());
        if {
            &&& u64::bytes_parseable(journal_entries_crc_bytes)
            &&& journal_entries_crc_bytes == spec_crc_bytes(journal_entries)
        } {
            Some(journal_entries)
        }
        else {
            None
        }
    }
    else {
        None
    }
}

pub(super) open spec fn parse_journal_entry(entries_bytes: Seq<u8>, start: int) -> Option<(JournalEntry, int)>
    recommends
        0 <= start <= entries_bytes.len(),
    decreases
        entries_bytes.len() - start
{
    if start + u64::spec_size_of() + u64::spec_size_of() > entries_bytes.len() {
        None
    }
    else {
        let addr_bytes = opaque_section(entries_bytes, start, u64::spec_size_of());
        let addr = u64::spec_from_bytes(addr_bytes);
        let length_offset = start + u64::spec_size_of();
        let length_bytes = opaque_section(entries_bytes, length_offset, u64::spec_size_of());
        let length = u64::spec_from_bytes(length_bytes);
        let data_offset = length_offset + u64::spec_size_of();
        if data_offset + length > entries_bytes.len() {
            None
        }
        else {
            let data = opaque_section(entries_bytes, data_offset, length as nat);
            let entry = JournalEntry { start: addr as int, bytes_to_write: data };
            Some((entry, data_offset + length))
        }
    }
}

pub(super) open spec fn parse_journal_entries(entries_bytes: Seq<u8>, start: int) -> Option<Seq<JournalEntry>>
    recommends
        0 <= start <= entries_bytes.len(),
    decreases
        entries_bytes.len() - start
{
    if !(0 <= start <= entries_bytes.len()) {
        None
    }
    else if start == entries_bytes.len() {
        Some(Seq::<JournalEntry>::empty())
    }
    else {
        match parse_journal_entry(entries_bytes, start) {
            None => None,
            Some((entry, next)) =>
                match parse_journal_entries(entries_bytes, next) {
                    None => None,
                    Some(remaining_journal) => Some(seq![entry] + remaining_journal),
                },
        }
    }
}

pub(super) open spec fn recover_journal_entries(bytes: Seq<u8>, sm: JournalStaticMetadata, journal_length: u64)
    -> Option<Seq<JournalEntry>>
{
    match recover_journal_entries_bytes(bytes, sm, journal_length) {
        None => None,
        Some(entries_bytes) => parse_journal_entries(entries_bytes, 0),
    }
}

pub(super) open spec fn apply_journal_entry(bytes: Seq<u8>, entry: JournalEntry, sm: JournalStaticMetadata)
                                     -> Option<Seq<u8>>
{
    if entry.fits(sm) {
        Some(opaque_update_bytes(bytes, entry.start, entry.bytes_to_write))
    }
    else {
        None
    }
}

pub(super) open spec fn apply_journal_entries(bytes: Seq<u8>, entries: Seq<JournalEntry>, starting_entry: int,
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

pub(super) open spec fn recover_storage_state_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    match recover_journal_length(bytes, sm) {
        None => None,
        Some(journal_length) => {
            match recover_journal_entries(bytes, sm, journal_length) {
                None => None,
                Some(journal_entries) => apply_journal_entries(bytes, journal_entries, 0, sm),
            }
        },
    }
}

pub(super) open spec fn recover_committed_cdb(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<bool>
{
    recover_cdb(bytes, sm.committed_cdb_start as int)
}

pub(super) open spec fn recover_storage_state(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    match recover_committed_cdb(bytes, sm) {
        None => None,
        Some(c) => if c { recover_storage_state_case_committed(bytes, sm) } else { Some(bytes) },
    }
}

pub(super) open spec fn recover_journal(bytes: Seq<u8>) -> Option<RecoveredJournal>
{
    match recover_version_metadata(bytes) {
        None => None,
        Some(vm) =>
            match recover_static_metadata(bytes, vm) {
                None => None,
                Some(sm) =>
                    match recover_storage_state(bytes, sm) {
                        None => None,
                        Some(state) =>
                            Some(RecoveredJournal {
                                constants: JournalConstants {
                                    app_version_number: sm.app_version_number,
                                    app_program_guid: sm.app_program_guid,
                                    journal_capacity: (sm.journal_entries_end - sm.journal_entries_start) as u64,
                                    app_area_start: sm.app_area_start,
                                    app_area_end: sm.app_area_end,
                                },
                                state,
                            }),
                    },
            },
    }
}

}
