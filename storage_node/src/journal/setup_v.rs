use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::traits_t::size_of;
use crate::common::align_v::*;
use crate::common::nonlinear_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use super::recover_v::*;
use super::spec_v::*;

verus! {

pub(super) exec fn get_space_needed_for_journal_entries(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
) -> (result: OverflowingU64)
    ensures
        0 <= result@,
        result@ == space_needed_for_journal_entries(max_journal_entries as int, max_journaled_bytes as int),
{
    reveal(opaque_mul);
    let num_journaled_bytes = OverflowingU64::new(max_journaled_bytes);
    let journal_entry_size = OverflowingU64::new(size_of::<u64>() as u64).add(size_of::<u64>() as u64);
    let num_header_bytes = OverflowingU64::new(max_journal_entries).mul_overflowing_u64(&journal_entry_size);
    num_journaled_bytes.add_overflowing_u64(&num_header_bytes)
}

pub closed spec fn spec_space_needed_for_setup(ps: JournalSetupParameters) -> int
    recommends
        ps.valid(),
{
    let journal_size = space_needed_for_journal_entries(ps.max_journal_entries as int, ps.max_journaled_bytes as int);
    let journal_version_metadata_start: int = 0;
    let journal_version_metadata_end = JournalVersionMetadata::spec_size_of() as int;
    let (journal_version_metadata_crc_start, journal_version_metadata_crc_end) =
        spec_allocate_space::<u64>(journal_version_metadata_end);
    let (journal_static_metadata_start, journal_static_metadata_end) =
        spec_allocate_space::<JournalStaticMetadata>(journal_version_metadata_crc_end);
    let (journal_static_metadata_crc_start, journal_static_metadata_crc_end) =
        spec_allocate_space::<u64>(journal_static_metadata_end);
    let (committed_cdb_start, committed_cdb_end) = spec_allocate_space::<u64>(journal_static_metadata_crc_end);
    let (journal_length_start, journal_length_end) = spec_allocate_space::<u64>(committed_cdb_end);
    let (journal_length_crc_start, journal_length_crc_end) = spec_allocate_space::<u64>(journal_length_end);
    let (journal_entries_crc_start, journal_entries_crc_end) = spec_allocate_space::<u64>(journal_length_crc_end);
    let (journal_entries_start, journal_entries_end) =
        spec_allocate_specified_space(journal_entries_crc_end, journal_size, u64::spec_size_of() as int);
    let (app_area_start, min_app_area_end) =
        spec_allocate_specified_space(journal_entries_end, ps.app_area_size as int, ps.app_area_alignment as int);
    min_app_area_end
}

#[verifier::ext_equal]
pub(super) struct AddressesForSetup
{
    pub(super) journal_version_metadata_start: u64,
    pub(super) journal_version_metadata_crc_start: u64,
    pub(super) journal_static_metadata_start: u64,
    pub(super) journal_static_metadata_end: u64,
    pub(super) journal_static_metadata_crc_start: u64,
    pub(super) journal_dynamic_area_start: u64,
    pub(super) committed_cdb_start: u64,
    pub(super) journal_length_start: u64,
    pub(super) journal_length_crc_start: u64,
    pub(super) journal_entries_crc_start: u64,
    pub(super) journal_entries_start: u64,
    pub(super) journal_entries_end: u64,
    pub(super) app_area_start: u64,
    pub(super) min_app_area_end: u64,
}

impl AddressesForSetup
{
    pub(super) open spec fn valid(&self, ps: JournalSetupParameters) -> bool
    {
        let journal_size = space_needed_for_journal_entries(ps.max_journal_entries as int, ps.max_journaled_bytes as int);
        let space_needed_for_setup = spec_space_needed_for_setup(ps);
        &&& self.journal_version_metadata_start == spec_journal_version_metadata_start()
        &&& self.journal_version_metadata_start + JournalVersionMetadata::spec_size_of()
                <= self.journal_version_metadata_crc_start
        &&& self.journal_version_metadata_crc_start == spec_journal_version_metadata_crc_start()
        &&& opaque_aligned(self.journal_version_metadata_crc_start as int, u64::spec_size_of() as int)
        &&& self.journal_version_metadata_crc_start ==
            round_up_to_alignment(self.journal_version_metadata_start + JournalVersionMetadata::spec_size_of(),
                                  u64::spec_align_of() as int)
        &&& self.journal_version_metadata_crc_start + u64::spec_size_of() <= self.journal_static_metadata_start
        &&& self.journal_static_metadata_start == spec_journal_static_metadata_start()
        &&& opaque_aligned(self.journal_static_metadata_start as int, JournalStaticMetadata::spec_align_of() as int)
        &&& self.journal_static_metadata_start + JournalStaticMetadata::spec_size_of() ==
               self.journal_static_metadata_end
        &&& self.journal_static_metadata_end <= self.journal_static_metadata_crc_start
        &&& self.journal_static_metadata_crc_start == spec_journal_static_metadata_crc_start()
        &&& opaque_aligned(self.journal_static_metadata_crc_start as int, u64::spec_size_of() as int)
        &&& self.journal_static_metadata_crc_start + u64::spec_size_of() <= self.journal_dynamic_area_start
        &&& self.journal_dynamic_area_start <= self.committed_cdb_start
        &&& opaque_aligned(self.committed_cdb_start as int, const_persistence_chunk_size() as int)
        &&& self.committed_cdb_start + u64::spec_size_of() <= self.journal_length_start
        &&& self.journal_length_start + u64::spec_size_of() <= self.journal_length_crc_start
        &&& self.journal_length_crc_start + u64::spec_size_of() <= self.journal_entries_crc_start
        &&& self.journal_entries_crc_start + u64::spec_size_of() <= self.journal_entries_start
        &&& 0 <= journal_size
        &&& self.journal_entries_start + journal_size <= self.journal_entries_end
        &&& self.journal_entries_end <= self.app_area_start
        &&& opaque_aligned(self.app_area_start as int, ps.app_area_alignment as int)
        &&& self.app_area_start + ps.app_area_size == self.min_app_area_end
    }
}

pub(super) exec fn get_addresses_for_setup(ps: &JournalSetupParameters) -> (result: Option<AddressesForSetup>)
    requires
        ps.valid(),
    ensures
        match result {
            Some(v) => v.valid(*ps) && v.min_app_area_end == spec_space_needed_for_setup(*ps),
            None => u64::MAX < spec_space_needed_for_setup(*ps),
        }
{
    let journal_size = get_space_needed_for_journal_entries(ps.max_journal_entries, ps.max_journaled_bytes);

    let journal_version_metadata_end = OverflowingU64::new(size_of::<JournalVersionMetadata>() as u64);
    let (journal_version_metadata_crc_start, journal_version_metadata_crc_end) =
        allocate_space::<u64>(&journal_version_metadata_end);
    let (journal_static_metadata_start, journal_static_metadata_end) =
        allocate_space::<JournalStaticMetadata>(&journal_version_metadata_crc_end);
    let (journal_static_metadata_crc_start, journal_static_metadata_crc_end) =
        allocate_space::<u64>(&journal_static_metadata_end);
    let (committed_cdb_start, committed_cdb_end) = allocate_space::<u64>(&journal_static_metadata_crc_end);
    let (journal_length_start, journal_length_end) = allocate_space::<u64>(&committed_cdb_end);
    let (journal_length_crc_start, journal_length_crc_end) = allocate_space::<u64>(&journal_length_end);
    let (journal_entries_crc_start, journal_entries_crc_end) = allocate_space::<u64>(&journal_length_crc_end);
    let (journal_entries_start, journal_entries_end) =
        allocate_specified_space_overflowing_u64(&journal_entries_crc_end, &journal_size, size_of::<u64>() as u64);
    let (app_area_start, min_app_area_end) =
        allocate_specified_space(&journal_entries_end, ps.app_area_size, ps.app_area_alignment);

    if min_app_area_end.is_overflowed() {
        None
    }
    else {
        Some(AddressesForSetup {
            journal_version_metadata_start: 0,
            journal_version_metadata_crc_start: journal_version_metadata_crc_start.unwrap(),
            journal_static_metadata_start: journal_static_metadata_start.unwrap(),
            journal_static_metadata_end: journal_static_metadata_end.unwrap(),
            journal_static_metadata_crc_start: journal_static_metadata_crc_start.unwrap(),
            journal_dynamic_area_start: committed_cdb_start.unwrap(),
            committed_cdb_start: committed_cdb_start.unwrap(),
            journal_length_start: journal_length_start.unwrap(),
            journal_length_crc_start: journal_length_crc_start.unwrap(),
            journal_entries_crc_start: journal_entries_crc_start.unwrap(),
            journal_entries_start: journal_entries_start.unwrap(),
            journal_entries_end: journal_entries_end.unwrap(),
            app_area_start: app_area_start.unwrap(),
            min_app_area_end: min_app_area_end.unwrap(),
        })
    }
}

pub(super) proof fn lemma_setup_works(
    bytes: Seq<u8>,
    ps: JournalSetupParameters,
    addrs: AddressesForSetup,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata
)
    requires
        ps.valid(),
        addrs.valid(ps),
        validate_metadata(vm, sm, bytes.len()),
        vm.version_number == JOURNAL_PROGRAM_VERSION_NUMBER,
        vm.program_guid == JOURNAL_PROGRAM_GUID,
        sm.app_version_number == ps.app_version_number,
        sm.app_program_guid == ps.app_program_guid,
        sm.committed_cdb_start == addrs.committed_cdb_start,
        sm.journal_length_start == addrs.journal_length_start,
        sm.journal_length_crc_start == addrs.journal_length_crc_start,
        sm.journal_entries_start == addrs.journal_entries_start,
        sm.journal_entries_end == addrs.journal_entries_end,
        sm.app_area_start == addrs.app_area_start,
        sm.app_area_end >= addrs.min_app_area_end,
        sm.app_area_end == bytes.len(),
        ({
            &&& bytes.subrange(spec_journal_version_metadata_start(),
                              spec_journal_version_metadata_end()) == vm.spec_to_bytes()
            &&& bytes.subrange(spec_journal_version_metadata_crc_start(),
                              spec_journal_version_metadata_crc_end())
                    == spec_crc_bytes(vm.spec_to_bytes())
            &&& bytes.subrange(spec_journal_static_metadata_start(), spec_journal_static_metadata_end())
                    == sm.spec_to_bytes()
            &&& bytes.subrange(spec_journal_static_metadata_crc_start(), spec_journal_static_metadata_crc_end())
                    == spec_crc_bytes(sm.spec_to_bytes())
            &&& extract_section(bytes, sm.committed_cdb_start as int, u64::spec_size_of()) == u64::spec_to_bytes(CDB_FALSE)
        }),
    ensures ({
        &&& recover_journal(bytes) matches Some(j)
        &&& j.constants.app_version_number == ps.app_version_number
        &&& j.constants.app_program_guid == ps.app_program_guid
        &&& j.constants.journal_capacity == addrs.journal_entries_end - addrs.journal_entries_start
        &&& j.constants.app_area_start == sm.app_area_start
        &&& j.constants.app_area_end == sm.app_area_end
        &&& bytes == j.state
    }),
{
    broadcast use pmcopy_axioms;
}

pub(super) open spec fn spec_ready_for_app_setup(
    bytes: Seq<u8>,
    constants: JournalConstants,
) -> bool
{
    &&& recover_version_metadata(bytes) matches Some(vm)
    &&& recover_static_metadata(bytes, vm) matches Some(sm)
    &&& recover_committed_cdb(bytes, sm) == Some(false)
    &&& recover_journal(bytes) == Some(RecoveredJournal{ constants, state: bytes })
    &&& constants.app_area_start == sm.app_area_start
    &&& constants.app_area_end == sm.app_area_end
    &&& constants.app_area_end == bytes.len()
}

}
