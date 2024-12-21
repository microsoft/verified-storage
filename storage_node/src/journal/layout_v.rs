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
    pub program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

#[repr(C)]
#[derive(PmCopy, Copy, Default, Debug)]
pub struct JournalStaticMetadata {
    pub app_version_number: u64,
    pub committed_cdb_start: u64,
    pub journal_length_start: u64,
    pub journal_length_crc_start: u64,
    pub journal_entries_crc_start: u64,
    pub journal_entries_start: u64,
    pub journal_entries_end: u64,
    pub app_static_area_start: u64,
    pub app_static_area_end: u64,
    pub app_dynamic_area_start: u64,
    pub app_dynamic_area_end: u64,
    pub app_program_guid: u128, // TODO: Move to more natural position after pmcopy bug fix
}

pub struct JournalEntry
{
    pub start: int,
    pub bytes_to_write: Seq<u8>,
}

impl JournalEntry
{
    pub open spec fn end(self) -> int
    {
        self.start + self.bytes_to_write.len()
    }

    pub open spec fn addrs(self) -> Set<int>
    {
        Set::<int>::new(|i| self.start <= i < self.end())
    }
}

pub open spec fn spec_journal_version_metadata_start() -> int
{
    0
}

pub open spec fn spec_journal_version_metadata_end() -> int
{
    JournalVersionMetadata::spec_size_of() as int
}

pub open spec fn spec_journal_version_metadata_crc_start() -> int
{
    round_up_to_alignment(spec_journal_version_metadata_end(), u64::spec_align_of() as int)
}

pub open spec fn spec_journal_version_metadata_crc_end() -> int
{
    spec_journal_version_metadata_crc_start() + u64::spec_size_of() as int
}

pub open spec fn spec_journal_static_metadata_start() -> int
{
    round_up_to_alignment(spec_journal_version_metadata_crc_end(), JournalStaticMetadata::spec_align_of() as int)
}

pub open spec fn spec_journal_static_metadata_end() -> int
{
    spec_journal_static_metadata_start() + JournalStaticMetadata::spec_size_of()
}

pub open spec fn spec_journal_static_metadata_crc_start() -> int
{
    round_up_to_alignment(spec_journal_static_metadata_end(), u64::spec_align_of() as int)
}

pub open spec fn spec_journal_static_metadata_crc_end() -> int
{
    spec_journal_static_metadata_crc_start() + u64::spec_size_of() as int
}

pub open spec fn validate_version_metadata(m: JournalVersionMetadata) -> bool
{
    &&& spec_journal_version_metadata_end() <= spec_journal_version_metadata_crc_start()
    &&& m.program_guid == JOURNAL_PROGRAM_GUID
}

pub open spec fn recover_version_metadata(bytes: Seq<u8>) -> Option<JournalVersionMetadata>
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

pub open spec fn validate_static_metadata(sm: JournalStaticMetadata, vm: JournalVersionMetadata) -> bool
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
        &&& sm.journal_entries_end <= sm.app_static_area_start
        &&& sm.app_static_area_start <= sm.app_static_area_end
        &&& sm.app_static_area_end <= sm.app_dynamic_area_start
        &&& sm.app_dynamic_area_start <= sm.app_dynamic_area_end
    }
    else {
        false
    }
}

pub open spec fn recover_static_metadata(bytes: Seq<u8>, vm: JournalVersionMetadata)
                                         -> Option<JournalStaticMetadata>
{
    if spec_journal_static_metadata_crc_end() > bytes.len() {
        None
    }
    else {
        match recover_object::<JournalStaticMetadata>(bytes, spec_journal_static_metadata_start(),
                                                      spec_journal_static_metadata_crc_start()) {
            Some(sm) => if validate_static_metadata(sm, vm) && sm.app_dynamic_area_end <= bytes.len() {
                Some(sm)
            } else {
                None
            },
            None => None,
        }
    }
}

pub open spec fn recover_journal_length(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<u64>
{
    recover_object::<u64>(bytes, sm.journal_length_start as int, sm.journal_length_crc_start as int)
}

pub open spec fn recover_journal_entries_bytes(bytes: Seq<u8>, sm: JournalStaticMetadata, journal_length: u64)
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

pub open spec fn parse_journal_entry(entries_bytes: Seq<u8>, start: int) -> Option<(JournalEntry, int)>
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

pub open spec fn parse_journal_entries(entries_bytes: Seq<u8>, start: int) -> Option<Seq<JournalEntry>>
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

pub proof fn lemma_parse_journal_entry_relation_to_next(entries_bytes: Seq<u8>, start: int)
    requires
        parse_journal_entries(entries_bytes, start) is Some,
        parse_journal_entry(entries_bytes, start) is Some,
    ensures
        ({
            let (entry, next) = parse_journal_entry(entries_bytes, start).unwrap();
            &&& parse_journal_entries(entries_bytes, start).unwrap().len() > 0
            &&& parse_journal_entries(entries_bytes, next) is Some
            &&& parse_journal_entries(entries_bytes, start).unwrap()[0] == entry
            &&& parse_journal_entries(entries_bytes, next).unwrap() ==
                parse_journal_entries(entries_bytes, start).unwrap().skip(1)
        }),
{
    let (entry, next) = parse_journal_entry(entries_bytes, start).unwrap();
    assert(parse_journal_entries(entries_bytes, next).unwrap() =~=
           parse_journal_entries(entries_bytes, start).unwrap().skip(1));
}

pub proof fn lemma_parse_journal_entry_implications(
    entries_bytes: Seq<u8>,
    entries: Seq<JournalEntry>,
    num_entries_read: int,
    current_pos: int,
)
    requires
        parse_journal_entries(entries_bytes, 0) == Some(entries),
        0 <= num_entries_read < entries.len(),
        0 <= current_pos < entries_bytes.len(),
        parse_journal_entries(entries_bytes, current_pos) == Some(entries.skip(num_entries_read)),
        parse_journal_entry(entries_bytes, current_pos) is Some
    ensures ({
        let (entry, next_pos) = parse_journal_entry(entries_bytes, current_pos).unwrap();
        &&& num_entries_read + 1 == entries.len() <==> next_pos == entries_bytes.len()
        &&& entries[num_entries_read] == entry
        &&& parse_journal_entries(entries_bytes, next_pos) == Some(entries.skip(num_entries_read + 1))
    }),
{
    lemma_parse_journal_entry_relation_to_next(entries_bytes, current_pos);
    assert(entries.skip(num_entries_read + 1) =~= entries.skip(num_entries_read).skip(1));
}

pub open spec fn recover_journal_entries(bytes: Seq<u8>, sm: JournalStaticMetadata, journal_length: u64)
    -> Option<Seq<JournalEntry>>
{
    match recover_journal_entries_bytes(bytes, sm, journal_length) {
        None => None,
        Some(entries_bytes) => parse_journal_entries(entries_bytes, 0),
    }
}

pub open spec fn apply_journal_entry(bytes: Seq<u8>, entry: JournalEntry, sm: JournalStaticMetadata)
                                     -> Option<Seq<u8>>
{
    if {
        &&& 0 <= sm.app_dynamic_area_start <= entry.start
        &&& entry.end() <= sm.app_dynamic_area_end
    } {
        Some(opaque_update_bytes(bytes, entry.start, entry.bytes_to_write))
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

pub open spec fn recover_storage_state_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
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

pub open spec fn recover_committed_cdb(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<bool>
{
    recover_cdb(bytes, sm.committed_cdb_start as int)
}

pub open spec fn recover_storage_state(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    match recover_committed_cdb(bytes, sm) {
        None => None,
        Some(c) => if c { recover_storage_state_case_committed(bytes, sm) } else { Some(bytes) },
    }
}

#[verifier::opaque]
pub open spec fn recover_journal(bytes: Seq<u8>) -> Option<RecoveredJournal>
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
                                    app_static_area_start: sm.app_static_area_start,
                                    app_static_area_end: sm.app_static_area_end,
                                    app_dynamic_area_start: sm.app_dynamic_area_start,
                                    app_dynamic_area_end: sm.app_dynamic_area_end,
                                },
                                state,
                            }),
                    },
            },
    }
}

}
