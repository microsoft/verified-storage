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

spec fn spec_space_needed_for_journal(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
) -> int
{
    max_journaled_bytes as int + // journal data
    max_journal_entries * (u64::spec_size_of() as int + u64::spec_size_of() as int) + // entry headers
    u64::spec_size_of() as int // journal CRC
}

exec fn get_space_needed_for_journal(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
) -> (result: OverflowingU64)
    ensures
        0 <= result@,
        result@ == spec_space_needed_for_journal(max_journal_entries, max_journaled_bytes),
{
    let num_journaled_bytes = OverflowingU64::new(max_journaled_bytes);
    let journal_entry_size = OverflowingU64::new(size_of::<u64>() as u64).add(size_of::<u64>() as u64);
    let num_header_bytes = OverflowingU64::new(max_journal_entries).mul_overflowing_u64(&journal_entry_size);
    num_journaled_bytes.add_overflowing_u64(&num_header_bytes).add_usize(size_of::<u64>())
}

pub closed spec fn spec_space_needed_for_setup(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
) -> int
    recommends
        0 < app_static_area_alignment,
        0 < app_dynamic_area_alignment,
{
    let journal_size = spec_space_needed_for_journal(max_journal_entries, max_journaled_bytes);
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
    let (journal_data_start, journal_data_end) =
        spec_allocate_specified_space(journal_length_crc_end, journal_size, u64::spec_size_of() as int);
    let (app_static_area_start, app_static_area_end) =
        spec_allocate_specified_space(journal_data_end, app_static_area_size as int, app_static_area_alignment as int);
    let (app_dynamic_area_start, app_dynamic_area_end) =
        spec_allocate_specified_space(app_static_area_end, app_dynamic_area_size as int,
                                      app_dynamic_area_alignment as int);
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
    journal_data_start: u64,
    journal_data_end: u64,
    app_static_area_start: u64,
    app_static_area_end: u64,
    app_dynamic_area_start: u64,
    app_dynamic_area_end: u64,
}

impl AddressesForSetup
{
    spec fn valid(
        &self,
        max_journal_entries: u64,
        max_journaled_bytes: u64,
        app_static_area_size: u64,
        app_static_area_alignment: u64,
        app_dynamic_area_size: u64,
        app_dynamic_area_alignment: u64,
    ) -> bool
    {
        let journal_size = spec_space_needed_for_journal(max_journal_entries, max_journaled_bytes);
        let space_needed_for_setup = spec_space_needed_for_setup(
            max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
            app_dynamic_area_size, app_dynamic_area_alignment
        );
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
        &&& self.journal_length_crc_start + u64::spec_size_of() <= self.journal_data_start
        &&& 0 <= journal_size
        &&& self.journal_data_start + journal_size <= self.journal_data_end
        &&& self.journal_data_end <= self.app_static_area_start
        &&& opaque_aligned(self.app_static_area_start as int, app_static_area_alignment as int)
        &&& self.app_static_area_start + app_static_area_size == self.app_static_area_end
        &&& self.app_static_area_end <= self.app_dynamic_area_start
        &&& opaque_aligned(self.app_dynamic_area_start as int, app_dynamic_area_alignment as int)
        &&& self.app_dynamic_area_start + app_dynamic_area_size == self.app_dynamic_area_end
        &&& self.app_dynamic_area_end == space_needed_for_setup
    }
}

exec fn get_addresses_for_setup(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
) -> (result: Option<AddressesForSetup>)
    requires
        0 < app_static_area_alignment,
        0 < app_dynamic_area_alignment,
    ensures
        match result {
            Some(v) => v.valid(max_journal_entries, max_journaled_bytes, app_static_area_size,
                              app_static_area_alignment, app_dynamic_area_size, app_dynamic_area_alignment),
            None => u64::MAX < spec_space_needed_for_setup(
                max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
                app_dynamic_area_size, app_dynamic_area_alignment
            ),
        }
{
    let journal_size = get_space_needed_for_journal(max_journal_entries, max_journaled_bytes);

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
    let (journal_data_start, journal_data_end) =
        allocate_specified_space_overflowing_u64(&journal_length_crc_end, &journal_size, size_of::<u64>() as u64);
    let (app_static_area_start, app_static_area_end) =
        allocate_specified_space(&journal_data_end, app_static_area_size, app_static_area_alignment);
    let (app_dynamic_area_start, app_dynamic_area_end) =
        allocate_specified_space(&app_static_area_end, app_dynamic_area_size, app_dynamic_area_alignment);

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
            journal_data_start: journal_data_start.unwrap(),
            journal_data_end: journal_data_end.unwrap(),
            app_static_area_start: app_static_area_start.unwrap(),
            app_static_area_end: app_static_area_end.unwrap(),
            app_dynamic_area_start: app_dynamic_area_start.unwrap(),
            app_dynamic_area_end: app_dynamic_area_end.unwrap(),
        })
    }
}

pub exec fn get_space_needed_for_setup(
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
) -> (result: Option<u64>)
    requires
        0 < app_static_area_alignment,
        0 < app_dynamic_area_alignment,
    ensures
        ({
            let space_needed = spec_space_needed_for_setup(
                max_journal_entries, max_journaled_bytes,
                app_static_area_size, app_static_area_alignment,
                app_dynamic_area_size, app_dynamic_area_alignment
            );
            match result {
                Some(v) => v == space_needed,
                None => space_needed > u64::MAX,
            }
        })
{
    match get_addresses_for_setup(
        max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
        app_dynamic_area_size, app_dynamic_area_alignment
    ) {
        Some(addrs) => Some(addrs.app_dynamic_area_end),
        None => None
    }
}

proof fn lemma_setup_works(
    bytes: Seq<u8>,
    app_version_number: u64,
    app_program_guid: u128,
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
    addrs: AddressesForSetup,
    vm: JournalVersionMetadata,
    sm: JournalStaticMetadata
)
    requires
        0 < app_static_area_alignment,
        0 < app_dynamic_area_alignment,
        addrs.valid(max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
                    app_dynamic_area_size, app_dynamic_area_alignment),
        validate_version_metadata(vm),
        validate_static_metadata(sm, vm),
        vm.version_number == JOURNAL_PROGRAM_VERSION_NUMBER,
        vm.program_guid == JOURNAL_PROGRAM_GUID,
        sm.app_dynamic_area_end <= bytes.len(),
        sm.app_version_number == app_version_number,
        sm.app_program_guid == app_program_guid,
        sm.committed_cdb_start == addrs.committed_cdb_start,
        sm.journal_length_start == addrs.journal_length_start,
        sm.journal_length_crc_start == addrs.journal_length_crc_start,
        sm.journal_data_start == addrs.journal_data_start,
        sm.journal_data_end == addrs.journal_data_end,
        sm.app_static_area_start == addrs.app_static_area_start,
        sm.app_static_area_end == addrs.app_static_area_end,
        sm.app_dynamic_area_start == addrs.app_dynamic_area_start,
        sm.app_dynamic_area_end == addrs.app_dynamic_area_end,
        ({
            &&& opaque_subrange(bytes, spec_journal_version_metadata_start(), spec_journal_version_metadata_end()) == vm.spec_to_bytes()
            &&& opaque_subrange(bytes, spec_journal_version_metadata_crc_start(), spec_journal_version_metadata_crc_end())
                    == spec_crc_bytes(vm.spec_to_bytes())
            &&& opaque_subrange(bytes, spec_journal_static_metadata_start(), spec_journal_static_metadata_end())
                    == sm.spec_to_bytes()
            &&& opaque_subrange(bytes, spec_journal_static_metadata_crc_start(), spec_journal_static_metadata_crc_end())
                    == spec_crc_bytes(sm.spec_to_bytes())
            &&& opaque_section(bytes, sm.committed_cdb_start as int, u64::spec_size_of()) == u64::spec_to_bytes(CDB_FALSE)
        }),
    ensures ({
        &&& recover_journal(bytes) matches Some(j)
        &&& j.constants.app_version_number == app_version_number
        &&& j.constants.app_program_guid == app_program_guid
        &&& j.constants.app_static_area_start == sm.app_static_area_start
        &&& j.constants.app_static_area_end == sm.app_static_area_end
        &&& j.constants.app_dynamic_area_start == sm.app_dynamic_area_start
        &&& j.constants.app_dynamic_area_end == sm.app_dynamic_area_end
        &&& opaque_subrange(bytes, sm.app_static_area_start as int, sm.app_static_area_end as int) == j.app_static_area
        &&& opaque_subrange(bytes, sm.app_dynamic_area_start as int, sm.app_dynamic_area_end as int) == j.app_dynamic_area
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
    &&& recover_cdb(bytes, sm.committed_cdb_start as int) == Some(false)
    &&& recover_journal(bytes) matches Some(j)
    &&& j.constants == constants
    &&& constants.app_static_area_start == sm.app_static_area_start
    &&& constants.app_static_area_end == sm.app_static_area_end
    &&& constants.app_dynamic_area_start == sm.app_dynamic_area_start
    &&& constants.app_dynamic_area_end == sm.app_dynamic_area_end
    &&& constants.app_static_area_start <= constants.app_static_area_end
    &&& constants.app_static_area_end <= constants.app_dynamic_area_start
    &&& constants.app_dynamic_area_start <= constants.app_dynamic_area_end
    &&& constants.app_dynamic_area_start <= constants.app_dynamic_area_end
    &&& constants.app_dynamic_area_end <= bytes.len()
    &&& j.app_static_area == opaque_subrange(bytes, constants.app_static_area_start as int,
                                             constants.app_static_area_end as int)
    &&& j.app_dynamic_area == opaque_subrange(bytes, constants.app_dynamic_area_start as int,
                                              constants.app_dynamic_area_end as int)
}

pub exec fn begin_setup<PM>(
    pm: &mut PM,
    app_version_number: u64,
    app_program_guid: u128,
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
) -> (result: Result<JournalConstants, JournalError>)
    where
        PM: PersistentMemoryRegion
    requires
        old(pm).inv(),
    ensures
        pm.inv(),
        match result {
            Ok(constants) => {
                &&& 0 < app_static_area_alignment
                &&& 0 < app_dynamic_area_alignment
                &&& recover_journal(pm@.read_state) matches Some(j)
                &&& j.constants == constants
                &&& constants.app_version_number == app_version_number
                &&& constants.app_program_guid == app_program_guid
                &&& opaque_aligned(constants.app_static_area_start as int, app_static_area_alignment as int)
                &&& constants.app_static_area_end == constants.app_static_area_start + app_static_area_size
                &&& j.app_static_area == opaque_subrange(pm@.read_state, constants.app_static_area_start as int,
                                                         constants.app_static_area_end as int)
                &&& constants.app_static_area_end <= constants.app_dynamic_area_start
                &&& opaque_aligned(constants.app_dynamic_area_start as int, app_dynamic_area_alignment as int)
                &&& constants.app_dynamic_area_end == constants.app_dynamic_area_start + app_dynamic_area_size
                &&& constants.app_dynamic_area_end <= pm@.len()
                &&& j.app_dynamic_area == opaque_subrange(pm@.read_state, constants.app_dynamic_area_start as int,
                                                          constants.app_dynamic_area_end as int)
                &&& ready_for_app_setup(pm@.read_state, constants)
            },
            Err(JournalError::InvalidAlignment) => {
                ||| app_static_area_alignment == 0
                ||| app_dynamic_area_alignment == 0
            },
            Err(JournalError::NotEnoughSpace) => {
                let space_needed = spec_space_needed_for_setup(max_journal_entries, max_journaled_bytes,
                                                               app_static_area_size, app_static_area_alignment,
                                                               app_dynamic_area_size, app_dynamic_area_alignment);
                &&& 0 < app_static_area_alignment
                &&& 0 < app_dynamic_area_alignment
                &&& pm@.len() < space_needed
            },
            Err(_) => false,
        }
{
    if app_static_area_alignment == 0 || app_dynamic_area_alignment == 0 {
        return Err(JournalError::InvalidAlignment);
    }

    // Compute the region size so we can see if we have enough space.
    // This also establishes that the region size fits in a u64, so
    // if it turns out we need more than u64::MAX bytes we're justified
    // in returning `JournalError::NotEnoughSpace`.
    let pm_size = pm.get_region_size();

    let addrs = match get_addresses_for_setup(
        max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
        app_dynamic_area_size, app_dynamic_area_alignment
    ) {
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
        assert(addrs.valid(max_journal_entries, max_journaled_bytes, app_static_area_size, app_static_area_alignment,
                           app_dynamic_area_size, app_dynamic_area_alignment));
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
        app_version_number,
        app_program_guid,
        committed_cdb_start: addrs.committed_cdb_start,
        journal_length_start: addrs.journal_length_start,
        journal_length_crc_start: addrs.journal_length_crc_start,
        journal_data_start: addrs.journal_data_start,
        journal_data_end: addrs.journal_data_end,
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
        lemma_setup_works(pm@.read_state,
                          app_version_number, app_program_guid, max_journal_entries,
                          max_journaled_bytes, app_static_area_size, app_static_area_alignment,
                          app_dynamic_area_size, app_dynamic_area_alignment,
                          addrs, vm, sm);
    }

    let journal_constants = JournalConstants {
        app_version_number,
        app_program_guid,
        app_static_area_start: addrs.app_static_area_start,
        app_static_area_end: addrs.app_static_area_end,
        app_dynamic_area_start: addrs.app_dynamic_area_start,
        app_dynamic_area_end: addrs.app_dynamic_area_end,
    };

    Ok(journal_constants)
}

pub proof fn end_setup(
    journal_constants: JournalConstants,
    state_before_app_setup: Seq<u8>,
    state_after_app_setup: Seq<u8>,
)
    requires
        ready_for_app_setup(state_before_app_setup, journal_constants),
        state_after_app_setup.len() == state_before_app_setup.len(),
        opaque_subrange(state_before_app_setup, 0, journal_constants.app_static_area_start as int)
            == opaque_subrange(state_after_app_setup, 0, journal_constants.app_static_area_start as int),
    ensures
        ({
            &&& recover_journal(state_after_app_setup) matches Some(j)
            &&& j.constants == journal_constants
            &&& j.app_static_area == opaque_subrange(state_after_app_setup,
                                                   journal_constants.app_static_area_start as int,
                                                   journal_constants.app_static_area_end as int)
            &&& j.app_dynamic_area == opaque_subrange(state_after_app_setup,
                                                    journal_constants.app_dynamic_area_start as int,
                                                    journal_constants.app_dynamic_area_end as int)
        }),
{
    lemma_auto_opaque_subrange_subrange(state_before_app_setup, 0, journal_constants.app_static_area_start as int);
    lemma_auto_opaque_subrange_subrange(state_after_app_setup, 0, journal_constants.app_static_area_start as int);
    reveal(recover_journal);
}

}
