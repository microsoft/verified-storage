use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::{size_of, align_of};
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use super::layout_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

pub closed spec fn spec_space_needed_for_journal_entries(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
) -> int
{
    max_journaled_bytes as int + // journal data
    max_journal_entries * (u64::spec_size_of() as int + u64::spec_size_of() as int) // entry headers
}

exec fn get_space_needed_for_journal_entries(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
) -> (result: OverflowingU64)
    ensures
        0 <= result@,
        result@ == spec_space_needed_for_journal_entries(max_journal_entries, max_journaled_bytes),
{
    let num_journaled_bytes = OverflowingU64::new(max_journaled_bytes);
    let journal_entry_size = OverflowingU64::new(size_of::<u64>() as u64).add(size_of::<u64>() as u64);
    let num_header_bytes = OverflowingU64::new(max_journal_entries).mul_overflowing_u64(&journal_entry_size);
    num_journaled_bytes.add_overflowing_u64(&num_header_bytes)
}

pub closed spec fn spec_space_needed_for_setup(ps: JournalSetupParameters) -> int
    recommends
        ps.valid(),
{
    let journal_size = spec_space_needed_for_journal_entries(ps.max_journal_entries, ps.max_journaled_bytes);
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
    let (app_static_area_start, app_static_area_end) =
        spec_allocate_specified_space(journal_entries_end, ps.app_static_area_size as int,
                                      ps.app_static_area_alignment as int);
    let (app_dynamic_area_start, app_dynamic_area_end) =
        spec_allocate_specified_space(app_static_area_end, ps.app_dynamic_area_size as int,
                                      ps.app_dynamic_area_alignment as int);
    app_dynamic_area_end
}

struct AddressesForSetup
{
    journal_version_metadata_start: u64,
    journal_version_metadata_crc_start: u64,
    journal_static_metadata_start: u64,
    journal_static_metadata_end: u64,
    journal_static_metadata_crc_start: u64,
    journal_dynamic_area_start: u64,
    committed_cdb_start: u64,
    journal_length_start: u64,
    journal_length_crc_start: u64,
    journal_entries_crc_start: u64,
    journal_entries_start: u64,
    journal_entries_end: u64,
    app_static_area_start: u64,
    app_static_area_end: u64,
    app_dynamic_area_start: u64,
    app_dynamic_area_end: u64,
}

impl AddressesForSetup
{
    spec fn valid(&self, ps: JournalSetupParameters) -> bool
    {
        let journal_size = spec_space_needed_for_journal_entries(ps.max_journal_entries, ps.max_journaled_bytes);
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
        &&& self.journal_entries_end <= self.app_static_area_start
        &&& opaque_aligned(self.app_static_area_start as int, ps.app_static_area_alignment as int)
        &&& self.app_static_area_start + ps.app_static_area_size == self.app_static_area_end
        &&& self.app_static_area_end <= self.app_dynamic_area_start
        &&& opaque_aligned(self.app_dynamic_area_start as int, ps.app_dynamic_area_alignment as int)
        &&& self.app_dynamic_area_start + ps.app_dynamic_area_size == self.app_dynamic_area_end
        &&& self.app_dynamic_area_end == space_needed_for_setup
    }
}

exec fn get_addresses_for_setup(ps: &JournalSetupParameters) -> (result: Option<AddressesForSetup>)
    requires
        ps.valid(),
    ensures
        match result {
            Some(v) => v.valid(*ps),
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
    let (app_static_area_start, app_static_area_end) =
        allocate_specified_space(&journal_entries_end, ps.app_static_area_size, ps.app_static_area_alignment);
    let (app_dynamic_area_start, app_dynamic_area_end) =
        allocate_specified_space(&app_static_area_end, ps.app_dynamic_area_size, ps.app_dynamic_area_alignment);

    if app_dynamic_area_end.is_overflowed() {
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
            app_static_area_start: app_static_area_start.unwrap(),
            app_static_area_end: app_static_area_end.unwrap(),
            app_dynamic_area_start: app_dynamic_area_start.unwrap(),
            app_dynamic_area_end: app_dynamic_area_end.unwrap(),
        })
    }
}

pub exec fn get_space_needed_for_setup(ps: &JournalSetupParameters) -> (result: Option<u64>)
    requires
        ps.valid(),
    ensures
        ({
            let space_needed = spec_space_needed_for_setup(*ps);
            match result {
                Some(v) => v == space_needed,
                None => space_needed > u64::MAX,
            }
        })
{
    match get_addresses_for_setup(ps) {
        Some(addrs) => Some(addrs.app_dynamic_area_end),
        None => None
    }
}

proof fn lemma_setup_works(
    bytes: Seq<u8>,
    ps: JournalSetupParameters,
    addrs: AddressesForSetup,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata
)
    requires
        ps.valid(),
        addrs.valid(ps),
        spec_journal_version_metadata_crc_end() <= bytes.len(),
        validate_version_metadata(vm),
        spec_journal_static_metadata_crc_end() <= bytes.len(),
        validate_static_metadata(sm, vm),
        vm.version_number == JOURNAL_PROGRAM_VERSION_NUMBER,
        vm.program_guid == JOURNAL_PROGRAM_GUID,
        sm.app_dynamic_area_end <= bytes.len(),
        sm.app_version_number == ps.app_version_number,
        sm.app_program_guid == ps.app_program_guid,
        sm.committed_cdb_start == addrs.committed_cdb_start,
        sm.journal_length_start == addrs.journal_length_start,
        sm.journal_length_crc_start == addrs.journal_length_crc_start,
        sm.journal_entries_start == addrs.journal_entries_start,
        sm.journal_entries_end == addrs.journal_entries_end,
        sm.app_static_area_start == addrs.app_static_area_start,
        sm.app_static_area_end == addrs.app_static_area_end,
        sm.app_dynamic_area_start == addrs.app_dynamic_area_start,
        sm.app_dynamic_area_end == addrs.app_dynamic_area_end,
        ({
            &&& opaque_subrange(bytes, spec_journal_version_metadata_start(),
                              spec_journal_version_metadata_end()) == vm.spec_to_bytes()
            &&& opaque_subrange(bytes, spec_journal_version_metadata_crc_start(),
                              spec_journal_version_metadata_crc_end())
                    == spec_crc_bytes(vm.spec_to_bytes())
            &&& opaque_subrange(bytes, spec_journal_static_metadata_start(), spec_journal_static_metadata_end())
                    == sm.spec_to_bytes()
            &&& opaque_subrange(bytes, spec_journal_static_metadata_crc_start(), spec_journal_static_metadata_crc_end())
                    == spec_crc_bytes(sm.spec_to_bytes())
            &&& opaque_section(bytes, sm.committed_cdb_start as int, u64::spec_size_of()) == u64::spec_to_bytes(CDB_FALSE)
        }),
    ensures ({
        &&& recover_journal(bytes) matches Some(j)
        &&& j.constants.app_version_number == ps.app_version_number
        &&& j.constants.app_program_guid == ps.app_program_guid
        &&& j.constants.journal_capacity == addrs.journal_entries_end - addrs.journal_entries_start
        &&& j.constants.app_static_area_start == sm.app_static_area_start
        &&& j.constants.app_static_area_end == sm.app_static_area_end
        &&& j.constants.app_dynamic_area_start == sm.app_dynamic_area_start
        &&& j.constants.app_dynamic_area_end == sm.app_dynamic_area_end
        &&& bytes == j.state
    }),
{
    broadcast use pmcopy_axioms;
    reveal(recover_journal);
}

pub closed spec fn ready_for_app_setup(
    bytes: Seq<u8>,
    constants: JournalConstants,
) -> bool
{
    &&& recover_version_metadata(bytes) matches Some(vm)
    &&& recover_static_metadata(bytes, vm) matches Some(sm)
    &&& recover_committed_cdb(bytes, sm) == Some(false)
    &&& recover_journal(bytes) == Some(RecoveredJournal{ constants, state: bytes })
    &&& constants.app_static_area_start == sm.app_static_area_start
    &&& constants.app_static_area_end == sm.app_static_area_end
    &&& constants.app_dynamic_area_start == sm.app_dynamic_area_start
    &&& constants.app_dynamic_area_end == sm.app_dynamic_area_end
    &&& constants.app_static_area_start <= constants.app_static_area_end
    &&& constants.app_static_area_end <= constants.app_dynamic_area_start
    &&& constants.app_dynamic_area_start <= constants.app_dynamic_area_end
    &&& constants.app_dynamic_area_start <= constants.app_dynamic_area_end
    &&& constants.app_dynamic_area_end <= bytes.len()
}

pub exec fn begin_setup<PM>(
    pm: &mut PM,
    ps: &JournalSetupParameters,
) -> (result: Result<JournalConstants, JournalError>)
    where
        PM: PersistentMemoryRegion
    requires
        old(pm).inv(),
    ensures
        pm.inv(),
        match result {
            Ok(constants) => {
                &&& ps.valid()
                &&& recover_journal(pm@.read_state) == Some(RecoveredJournal{ constants, state: pm@.read_state })
                &&& constants.app_version_number == ps.app_version_number
                &&& constants.app_program_guid == ps.app_program_guid
                &&& constants.journal_capacity
                       >= spec_space_needed_for_journal_entries(ps.max_journal_entries, ps.max_journaled_bytes)
                &&& opaque_aligned(constants.app_static_area_start as int, ps.app_static_area_alignment as int)
                &&& constants.app_static_area_end == constants.app_static_area_start + ps.app_static_area_size
                &&& constants.app_static_area_end <= constants.app_dynamic_area_start
                &&& opaque_aligned(constants.app_dynamic_area_start as int, ps.app_dynamic_area_alignment as int)
                &&& constants.app_dynamic_area_end == constants.app_dynamic_area_start + ps.app_dynamic_area_size
                &&& constants.app_dynamic_area_end <= pm@.len()
                &&& ready_for_app_setup(pm@.read_state, constants)
            },
            Err(JournalError::InvalidAlignment) => !ps.valid(),
            Err(JournalError::NotEnoughSpace) => {
                let space_needed = spec_space_needed_for_setup(*ps);
                &&& ps.valid()
                &&& pm@.len() < space_needed
            },
            Err(_) => false,
        }
{
    if ps.app_static_area_alignment == 0 || ps.app_dynamic_area_alignment == 0 {
        return Err(JournalError::InvalidAlignment);
    }

    // Compute the region size so we can see if we have enough space.
    // This also establishes that the region size fits in a u64, so
    // if it turns out we need more than u64::MAX bytes we're justified
    // in returning `JournalError::NotEnoughSpace`.
    let pm_size = pm.get_region_size();

    let addrs = match get_addresses_for_setup(ps) {
        Some(addrs) => addrs,
        None => { return Err(JournalError::NotEnoughSpace); }, // space needed > u64::MAX
    };

    if addrs.app_dynamic_area_end > pm_size {
        return Err(JournalError::NotEnoughSpace);
    }

    proof {
        assert(pm@.valid()) by { pm.lemma_inv_implies_view_valid(); }
        lemma_auto_can_result_from_write_effect_on_read_state();
        broadcast use pmcopy_axioms;
        assert(addrs.valid(*ps));
    }

    // We now know we have enough space, and we know the addresses to store things.

    let vm = JournalVersionMetadata{
        version_number: JOURNAL_PROGRAM_VERSION_NUMBER,
        program_guid: JOURNAL_PROGRAM_GUID,
    };
    pm.serialize_and_write(addrs.journal_version_metadata_start, &vm);

    let vm_crc = calculate_crc(&vm);
    pm.serialize_and_write(addrs.journal_version_metadata_crc_start, &vm_crc);
    
    let sm = JournalStaticMetadata{
        app_version_number: ps.app_version_number,
        app_program_guid: ps.app_program_guid,
        committed_cdb_start: addrs.committed_cdb_start,
        journal_length_start: addrs.journal_length_start,
        journal_length_crc_start: addrs.journal_length_crc_start,
        journal_entries_crc_start: addrs.journal_entries_crc_start,
        journal_entries_start: addrs.journal_entries_start,
        journal_entries_end: addrs.journal_entries_end,
        app_static_area_start: addrs.app_static_area_start,
        app_static_area_end: addrs.app_static_area_end,
        app_dynamic_area_start: addrs.app_dynamic_area_start,
        app_dynamic_area_end: addrs.app_dynamic_area_end,
    };
    pm.serialize_and_write(addrs.journal_static_metadata_start, &sm);
    let sm_crc = calculate_crc(&sm);
    pm.serialize_and_write(addrs.journal_static_metadata_crc_start, &sm_crc);

    let committed_cdb = CDB_FALSE;
    pm.serialize_and_write(addrs.committed_cdb_start, &committed_cdb);

    proof {
        lemma_auto_can_result_from_write_effect_on_read_state();
        lemma_setup_works(pm@.read_state, *ps, addrs, vm, sm);
    }

    let journal_constants = JournalConstants {
        app_version_number: ps.app_version_number,
        app_program_guid: ps.app_program_guid,
        journal_capacity: addrs.journal_entries_end - addrs.journal_entries_start,
        app_static_area_start: addrs.app_static_area_start,
        app_static_area_end: addrs.app_static_area_end,
        app_dynamic_area_start: addrs.app_dynamic_area_start,
        app_dynamic_area_end: addrs.app_dynamic_area_end,
    };

    Ok(journal_constants)
}

pub exec fn end_setup<PM>(
    pm: &mut PM,
    journal_constants: &JournalConstants,
    Ghost(state_after_begin_setup): Ghost<Seq<u8>>, // the state after calling `begin_setup` and
                                                    // before initializing the application state
)
    where
        PM: PersistentMemoryRegion
    requires
        old(pm).inv(),
        ready_for_app_setup(state_after_begin_setup, *journal_constants),
        old(pm)@.len() == state_after_begin_setup.len(),
        opaque_subrange(state_after_begin_setup, 0, journal_constants.app_static_area_start as int)
            == opaque_subrange(old(pm)@.read_state, 0, journal_constants.app_static_area_start as int),
    ensures
        pm.inv(),
        pm@.flush_predicted(),
        recover_journal(pm@.durable_state) ==
            Some(RecoveredJournal{ constants: *journal_constants, state: old(pm)@.read_state }),
{
    pm.flush();
    proof {
        lemma_auto_opaque_subrange_subrange(state_after_begin_setup, 0, journal_constants.app_static_area_start as int);
        lemma_auto_opaque_subrange_subrange(pm@.read_state, 0, journal_constants.app_static_area_start as int);
        reveal(recover_journal);
    }
}

}
