use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::align_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use super::entry_v::*;
use super::impl_v::*;
use super::spec_v::*;

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
pub(super) struct JournalVersionMetadata {
    pub program_guid: u128,
    pub version_number: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Default, Debug)]
#[verifier::ext_equal]
pub(super) struct JournalStaticMetadata {
    pub app_program_guid: u128,
    pub app_version_number: u64,
    pub committed_cdb_start: u64,
    pub journal_length_start: u64,
    pub journal_length_crc_start: u64,
    pub journal_entries_crc_start: u64,
    pub journal_entries_start: u64,
    pub journal_entries_end: u64,
    pub app_area_start: u64,
    pub app_area_end: u64,
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
        &&& is_aligned(sm.committed_cdb_start as int, const_persistence_chunk_size() as int)
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
    match recover_object::<u64>(bytes, sm.journal_length_start as int, sm.journal_length_crc_start as int) {
        None => None,
        Some(journal_length) =>
            if sm.journal_entries_start + journal_length <= sm.journal_entries_end {
                Some(journal_length)
            }
            else {
                None
            },
    }
}

pub(super) open spec fn recover_journal_entries_bytes(bytes: Seq<u8>, sm: JournalStaticMetadata, journal_length: u64)
    -> Option<Seq<u8>>
{
    recover_bytes(bytes, sm.journal_entries_start as int, journal_length as nat, sm.journal_entries_crc_start as int)
}

pub(super) open spec fn parse_journal_entry(entries_bytes: Seq<u8>) -> Option<(JournalEntry, int)>
{
    if u64::spec_size_of() + u64::spec_size_of() > entries_bytes.len() {
        None
    }
    else {
        let addr_bytes = extract_section(entries_bytes, 0, u64::spec_size_of());
        let addr = u64::spec_from_bytes(addr_bytes);
        let length_bytes = extract_section(entries_bytes, u64::spec_size_of() as int, u64::spec_size_of());
        let length = u64::spec_from_bytes(length_bytes);
        let data_offset = u64::spec_size_of() + u64::spec_size_of();
        if data_offset + length > entries_bytes.len() {
            None
        }
        else {
            let data = extract_section(entries_bytes, data_offset as int, length as nat);
            let entry = JournalEntry { start: addr as int, bytes_to_write: data };
            Some((entry, data_offset + length))
        }
    }
}

pub(super) open spec fn parse_journal_entries(entries_bytes: Seq<u8>) -> Option<Seq<JournalEntry>>
    decreases
        entries_bytes.len()
{
    if entries_bytes.len() == 0 {
        Some(Seq::<JournalEntry>::empty())
    }
    else {
        match parse_journal_entry(entries_bytes) {
            None => None,
            Some((entry, num_bytes)) =>
                match parse_journal_entries(entries_bytes.skip(num_bytes)) {
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
        Some(entries_bytes) => parse_journal_entries(entries_bytes),
    }
}

pub(super) open spec fn recover_storage_state_case_committed(bytes: Seq<u8>, sm: JournalStaticMetadata) -> Option<Seq<u8>>
{
    match recover_journal_length(bytes, sm) {
        None => None,
        Some(journal_length) => {
            match recover_journal_entries(bytes, sm, journal_length) {
                None => None,
                Some(journal_entries) => apply_journal_entries(bytes, journal_entries, sm),
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
                                    app_program_guid: sm.app_program_guid,
                                    app_version_number: sm.app_version_number,
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

pub(super) open spec fn spec_recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
{
    &&& recover_journal(state1) matches Some(j1)
    &&& recover_journal(state2) matches Some(j2)
    &&& j1.constants == j2.constants
    &&& seqs_match_in_range(j1.state, j2.state, j1.constants.app_area_start as int, j1.constants.app_area_end as int)
}

pub(super) open spec fn recovers_to(
    s: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    constants: JournalConstants,
) -> bool
{
    &&& recover_version_metadata(s) == Some(vm)
    &&& recover_static_metadata(s, vm) == Some(sm)
    &&& recover_committed_cdb(s, sm) == Some(false)
    &&& recover_journal(s) matches Some(j)
    &&& j.constants == constants
    &&& j.state == s
}

pub(super) proof fn lemma_recovery_doesnt_depend_on_journal_contents_when_uncommitted(
    s1: Seq<u8>,
    s2: Seq<u8>,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata,
    constants: JournalConstants,
)
    requires
        recovers_to(s1, vm, sm, constants),
        seqs_match_except_in_range(s1, s2, sm.journal_length_start as int, sm.journal_entries_end as int),
    ensures
        recovers_to(s2, vm, sm, constants),
{
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
}

impl <PM> Journal<PM>
where
    PM: PersistentMemoryRegion,
{
    pub proof fn lemma_recover_doesnt_change_size(bytes: Seq<u8>)
        ensures
            Self::recover(bytes) matches Some(j) ==> j.state.len() == bytes.len()
    {
        if recover_journal(bytes) is None {
            return;
        }

        let vm = recover_version_metadata(bytes).unwrap();
        let sm = recover_static_metadata(bytes, vm).unwrap();
        if recover_committed_cdb(bytes, sm) == Some(false) {
            return;
        }

        let journal_length = recover_journal_length(bytes, sm).unwrap();
        let entries = recover_journal_entries(bytes, sm, journal_length).unwrap();

        lemma_apply_journal_entries_doesnt_change_size(bytes, entries, sm);
    }

    pub proof fn lemma_recover_from_commit_idempotent(self)
        requires
            self.valid(),
        ensures
            Self::recover(self@.commit_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                        state: self@.commit_state }),
    {
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        lemma_apply_journal_entries_some_iff_journal_entries_valid(self@.read_state, self.entries@, self.sm);
        lemma_apply_journal_entries_only_affects_app_area(self@.read_state, self.vm@, self.sm, self.entries@);
    }
}

}
