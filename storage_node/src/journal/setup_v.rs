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
        &&& self.journal_version_metadata_start == 0
        &&& self.journal_version_metadata_start + JournalVersionMetadata::spec_size_of()
            <= self.journal_version_metadata_crc_start
        &&& opaque_aligned(self.journal_version_metadata_crc_start as int, u64::spec_size_of() as int)
        &&& self.journal_version_metadata_crc_start + u64::spec_size_of() <= self.journal_static_metadata_start
        &&& opaque_aligned(self.journal_static_metadata_start as int, JournalStaticMetadata::spec_align_of() as int)
        &&& self.journal_static_metadata_start + JournalStaticMetadata::spec_size_of() <= self.journal_static_metadata_end
        &&& self.journal_static_metadata_end <= self.journal_static_metadata_crc_start
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
        &&& self.app_static_area_start + app_static_area_size <= self.app_static_area_end
        &&& self.app_static_area_end <= self.app_dynamic_area_start
        &&& opaque_aligned(self.app_dynamic_area_start as int, app_dynamic_area_alignment as int)
        &&& self.app_dynamic_area_start + app_dynamic_area_size <= self.app_dynamic_area_end
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

proof fn lemma_setup_works(bytes: Seq<u8>, vm: JournalVersionMetadata, sm: JournalStaticMetadata)
    requires
        validate_version_metadata(vm),
        validate_static_metadata(sm, vm.journal_static_metadata_start as int, bytes.len()),
        opaque_section(bytes, 0, JournalVersionMetadata::spec_size_of()) == vm.spec_to_bytes(),
    ensures
        recover_journal(bytes) matches Some(app_dynamic_area) &&
           app_dynamic_area.len() == sm.app_dynamic_area_end - sm.app_dynamic_area_start,
{
    assume(false);
}

pub exec fn setup<PM>(
    pm: &mut PM,
    app_version_number: u64,
    app_program_guid: u128,
    max_journal_entries: u64,
    max_journaled_bytes: u64,
    app_static_area_size: u64,
    app_static_area_alignment: u64,
    app_dynamic_area_size: u64,
    app_dynamic_area_alignment: u64,
) -> (result: Result<bool, JournalError>)
    where
        PM: PersistentMemoryRegion
    requires
        old(pm).inv(),
    ensures
        match result {
            Ok(_) => {
                &&& 0 < app_static_area_alignment
                &&& 0 < app_dynamic_area_alignment
                &&& pm@.flush_predicted()
                &&& recover_journal(pm@.read_state) matches Some(app_dynamic_area)
                &&& app_dynamic_area.len() == app_dynamic_area_size
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
    }

    // We now know we have enough space, and we know the addresses to store things.

    let vm = JournalVersionMetadata{
        version_number: JOURNAL_PROGRAM_VERSION_NUMBER,
        journal_static_metadata_start: addrs.journal_static_metadata_start,
        journal_static_metadata_end: addrs.journal_static_metadata_end,
        journal_static_metadata_crc_start: addrs.journal_static_metadata_crc_start,
        journal_dynamic_area_start: addrs.journal_dynamic_area_start,
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

    pm.flush();

    proof {
        lemma_auto_can_result_from_write_effect_on_read_state();
        lemma_setup_works(pm@.read_state, vm, sm);
    }
    assume(false);
    Ok(true)
}

}
