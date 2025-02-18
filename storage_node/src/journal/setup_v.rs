use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use super::*;
use super::recover_v::*;
use super::spec_v::*;

verus! {

#[verifier::ext_equal]
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
}

impl AddressesForSetup
{
    spec fn valid(&self, journal_capacity: u64) -> bool
    {
        &&& self.journal_version_metadata_start == spec_journal_version_metadata_start()
        &&& self.journal_version_metadata_start + JournalVersionMetadata::spec_size_of()
                <= self.journal_version_metadata_crc_start
        &&& self.journal_version_metadata_crc_start == spec_journal_version_metadata_crc_start()
        &&& is_aligned(self.journal_version_metadata_crc_start as int, u64::spec_size_of() as int)
        &&& self.journal_version_metadata_crc_start ==
            round_up_to_alignment(self.journal_version_metadata_start + JournalVersionMetadata::spec_size_of(),
                                  u64::spec_align_of() as int)
        &&& self.journal_version_metadata_crc_start + u64::spec_size_of() <= self.journal_static_metadata_start
        &&& self.journal_static_metadata_start == spec_journal_static_metadata_start()
        &&& is_aligned(self.journal_static_metadata_start as int, JournalStaticMetadata::spec_align_of() as int)
        &&& self.journal_static_metadata_start + JournalStaticMetadata::spec_size_of() ==
               self.journal_static_metadata_end
        &&& self.journal_static_metadata_end <= self.journal_static_metadata_crc_start
        &&& self.journal_static_metadata_crc_start == spec_journal_static_metadata_crc_start()
        &&& is_aligned(self.journal_static_metadata_crc_start as int, u64::spec_size_of() as int)
        &&& self.journal_static_metadata_crc_start + u64::spec_size_of() <= self.journal_dynamic_area_start
        &&& self.journal_dynamic_area_start <= self.committed_cdb_start
        &&& is_aligned(self.committed_cdb_start as int, const_persistence_chunk_size() as int)
        &&& self.committed_cdb_start + u64::spec_size_of() <= self.journal_length_start
        &&& self.journal_length_start + u64::spec_size_of() <= self.journal_length_crc_start
        &&& self.journal_length_crc_start + u64::spec_size_of() <= self.journal_entries_crc_start
        &&& self.journal_entries_crc_start + u64::spec_size_of() <= self.journal_entries_start
        &&& self.journal_entries_start + journal_capacity == self.journal_entries_end
    }
}

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub closed spec fn spec_space_needed_for_setup(journal_capacity: nat) -> nat
    {
        let journal_version_metadata_start: int = 0;
        let journal_version_metadata_end = JournalVersionMetadata::spec_size_of() as int;
        let (journal_version_metadata_crc_start, journal_version_metadata_crc_end) =
            spec_reserve_space::<u64>(journal_version_metadata_end);
        let (journal_static_metadata_start, journal_static_metadata_end) =
            spec_reserve_space::<JournalStaticMetadata>(journal_version_metadata_crc_end);
        let (journal_static_metadata_crc_start, journal_static_metadata_crc_end) =
            spec_reserve_space::<u64>(journal_static_metadata_end);
        let (committed_cdb_start, committed_cdb_end) = spec_reserve_space::<u64>(journal_static_metadata_crc_end);
        let (journal_length_start, journal_length_end) = spec_reserve_space::<u64>(committed_cdb_end);
        let (journal_length_crc_start, journal_length_crc_end) = spec_reserve_space::<u64>(journal_length_end);
        let (journal_entries_crc_start, journal_entries_crc_end) = spec_reserve_space::<u64>(journal_length_crc_end);
        let (journal_entries_start, journal_entries_end) =
            spec_reserve_specified_space(journal_entries_crc_end, journal_capacity as int, u64::spec_size_of() as int);
        journal_entries_end as nat
    }
    
    pub exec fn space_needed_for_setup(journal_capacity: &OverflowableU64) -> (result: OverflowableU64)
        ensures
            result@ == Self::spec_space_needed_for_setup(journal_capacity@),
            journal_capacity@ <= result@,
    {
        let journal_version_metadata_end = OverflowableU64::new(size_of::<JournalVersionMetadata>() as u64);
        let (journal_version_metadata_crc_start, journal_version_metadata_crc_end) =
            reserve_space::<u64>(&journal_version_metadata_end);
        let (journal_static_metadata_start, journal_static_metadata_end) =
            reserve_space::<JournalStaticMetadata>(&journal_version_metadata_crc_end);
        let (journal_static_metadata_crc_start, journal_static_metadata_crc_end) =
            reserve_space::<u64>(&journal_static_metadata_end);
        let (committed_cdb_start, committed_cdb_end) = reserve_space::<u64>(&journal_static_metadata_crc_end);
        let (journal_length_start, journal_length_end) = reserve_space::<u64>(&committed_cdb_end);
        let (journal_length_crc_start, journal_length_crc_end) = reserve_space::<u64>(&journal_length_end);
        let (journal_entries_crc_start, journal_entries_crc_end) = reserve_space::<u64>(&journal_length_crc_end);
        let (journal_entries_start, journal_entries_end) =
            reserve_specified_space_overflowable_u64(&journal_entries_crc_end, &journal_capacity, size_of::<u64>() as u64);
        journal_entries_end
    }
    
    exec fn get_addresses_for_setup(journal_capacity: u64) -> (result: Option<AddressesForSetup>)
        ensures
            match result {
                Some(addrs) => {
                    &&& addrs.valid(journal_capacity)
                    &&& addrs.journal_entries_end == Self::spec_space_needed_for_setup(journal_capacity as nat)
                },
                None => u64::MAX < Self::spec_space_needed_for_setup(journal_capacity as nat),
            }
    {
        let journal_version_metadata_end = OverflowableU64::new(size_of::<JournalVersionMetadata>() as u64);
        let (journal_version_metadata_crc_start, journal_version_metadata_crc_end) =
            reserve_space::<u64>(&journal_version_metadata_end);
        let (journal_static_metadata_start, journal_static_metadata_end) =
            reserve_space::<JournalStaticMetadata>(&journal_version_metadata_crc_end);
        let (journal_static_metadata_crc_start, journal_static_metadata_crc_end) =
            reserve_space::<u64>(&journal_static_metadata_end);
        let (committed_cdb_start, committed_cdb_end) = reserve_space::<u64>(&journal_static_metadata_crc_end);
        let (journal_length_start, journal_length_end) = reserve_space::<u64>(&committed_cdb_end);
        let (journal_length_crc_start, journal_length_crc_end) = reserve_space::<u64>(&journal_length_end);
        let (journal_entries_crc_start, journal_entries_crc_end) = reserve_space::<u64>(&journal_length_crc_end);
        let (journal_entries_start, journal_entries_end) =
            reserve_specified_space(&journal_entries_crc_end, journal_capacity, size_of::<u64>() as u64);
    
        if journal_entries_end.is_overflowed() {
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
            })
        }
    }
    
    proof fn lemma_setup_works(
        bytes: Seq<u8>,
        jc: JournalConstants,
        addrs: AddressesForSetup,
        vm: JournalVersionMetadata,
        sm: JournalStaticMetadata
    )
        requires
            addrs.valid(jc.journal_capacity),
            addrs.journal_entries_end <= jc.app_area_start <= jc.app_area_end <= bytes.len(),
            validate_metadata(vm, sm, bytes.len()),
            vm.program_guid == JOURNAL_PROGRAM_GUID,
            vm.version_number == JOURNAL_PROGRAM_VERSION_NUMBER,
            sm.app_program_guid == jc.app_program_guid,
            sm.app_version_number == jc.app_version_number,
            sm.committed_cdb_start == addrs.committed_cdb_start,
            sm.journal_length_start == addrs.journal_length_start,
            sm.journal_length_crc_start == addrs.journal_length_crc_start,
            sm.journal_entries_start == addrs.journal_entries_start,
            sm.journal_entries_end == addrs.journal_entries_end,
            sm.app_area_start == jc.app_area_start,
            sm.app_area_end == jc.app_area_end,
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
                &&& extract_section(bytes, sm.committed_cdb_start as int, u64::spec_size_of())
                    == u64::spec_to_bytes(CDB_FALSE)
            }),
        ensures ({
            &&& recover_journal(bytes) matches Some(j)
            &&& j.constants == jc
            &&& j.constants.journal_capacity == addrs.journal_entries_end - addrs.journal_entries_start
            &&& bytes == j.state
        }),
    {
        broadcast use pmcopy_axioms;
    }
    
    pub exec fn setup(
        pm: &mut PM,
        jc: &JournalConstants,
    ) -> (result: Result<(), JournalError>)
        requires
            old(pm).inv(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            match result {
                Ok(constants) => {
                    &&& pm@.flush_predicted()
                    &&& Self::recover(pm@.durable_state)
                        == Some(RecoveredJournal{ constants: *jc, state: pm@.durable_state })
                    &&& jc.app_area_start <= jc.app_area_end
                    &&& jc.app_area_end == pm@.len()
                    &&& seqs_match_in_range(old(pm)@.read_state, pm@.read_state, jc.app_area_start as int,
                                           jc.app_area_end as int)
                },
                Err(JournalError::InvalidSetupParameters) => {
                    &&& pm@ == old(pm)@
                    &&& {
                           ||| jc.app_area_start > jc.app_area_end
                           ||| jc.app_area_end != pm@.len()
                       }
                },
                Err(JournalError::NotEnoughSpace) => {
                    &&& pm@ == old(pm)@
                    &&& jc.app_area_start < Self::spec_space_needed_for_setup(jc.journal_capacity as nat)
                },
                Err(_) => false,
            }
    {
        if jc.app_area_start > jc.app_area_end {
            return Err(JournalError::InvalidSetupParameters);
        }
    
        // Compute the region size so we can see if we have enough space.
        // This also establishes that the region size fits in a u64, so
        // if it turns out we need more than u64::MAX bytes we're justified
        // in returning `JournalError::NotEnoughSpace`.
        let pm_size = pm.get_region_size();
    
        if jc.app_area_end != pm_size {
            return Err(JournalError::InvalidSetupParameters);
        }
    
        let addrs = match Self::get_addresses_for_setup(jc.journal_capacity) {
            Some(addrs) => addrs,
            None => { return Err(JournalError::NotEnoughSpace); }, // space needed > u64::MAX
        };
    
        if addrs.journal_entries_end > jc.app_area_start {
            return Err(JournalError::NotEnoughSpace);
        }
    
        proof {
            assert(pm@.valid()) by { pm.lemma_inv_implies_view_valid(); }
            broadcast use pmcopy_axioms;
            assert(addrs.valid(jc.journal_capacity));
        }
    
        // We now know we have enough space, and we know the addresses to store things.
    
        broadcast use group_can_result_from_write_effect;
    
        let vm = JournalVersionMetadata{
            program_guid: JOURNAL_PROGRAM_GUID,
            version_number: JOURNAL_PROGRAM_VERSION_NUMBER,
        };
        pm.serialize_and_write(addrs.journal_version_metadata_start, &vm);
        let vm_crc = calculate_crc(&vm);
        pm.serialize_and_write(addrs.journal_version_metadata_crc_start, &vm_crc);
        
        let sm = JournalStaticMetadata{
            app_program_guid: jc.app_program_guid,
            app_version_number: jc.app_version_number,
            committed_cdb_start: addrs.committed_cdb_start,
            journal_length_start: addrs.journal_length_start,
            journal_length_crc_start: addrs.journal_length_crc_start,
            journal_entries_crc_start: addrs.journal_entries_crc_start,
            journal_entries_start: addrs.journal_entries_start,
            journal_entries_end: addrs.journal_entries_end,
            app_area_start: jc.app_area_start,
            app_area_end: jc.app_area_end,
        };
        pm.serialize_and_write(addrs.journal_static_metadata_start, &sm);
        let sm_crc = calculate_crc(&sm);
        pm.serialize_and_write(addrs.journal_static_metadata_crc_start, &sm_crc);
    
        let committed_cdb = CDB_FALSE;
        pm.serialize_and_write(addrs.committed_cdb_start, &committed_cdb);
    
        proof {
            Self::lemma_setup_works(pm@.read_state, *jc, addrs, vm, sm);
        }
    
        pm.flush();
    
        Ok(())
    }
}

}
