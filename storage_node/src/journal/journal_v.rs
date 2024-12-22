use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::pmem::wrpm_t::*;
use super::layout_v::*;
use super::setup_v::*;
use super::spec_v::*;
use deps_hack::PmCopy;

verus! {

pub enum JournalStatus {
    Quiescent
}

pub struct Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub(super) wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    pub(super) vm: Ghost<JournalVersionMetadata>,
    pub(super) sm: JournalStaticMetadata,
    pub(super) status: JournalStatus,
    pub(super) constants: JournalConstants,
    pub(super) commit_state: Ghost<Seq<u8>>,
    pub(super) journal_length: u64,
    pub(super) journaled_addrs: Ghost<Set<int>>,
    pub(super) entries: Ghost<Seq<JournalEntry>>,
}

impl<Perm, PM> View for Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    type V = JournalView;
    
    closed spec fn view(&self) -> JournalView
    {
        JournalView{
            constants: self.constants,
            durable_state: self.wrpm@.durable_state,
            read_state: self.wrpm@.read_state,
            commit_state: self.commit_state@,
            remaining_capacity: self.constants.journal_capacity - self.journal_length,
            journaled_addrs: self.journaled_addrs@,
        }
    }
}

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub closed spec fn valid(self) -> bool
    {
        self.valid_internal()
    }

    pub closed spec fn recover(bytes: Seq<u8>) -> Option<RecoveredJournal>
    {
        recover_journal(bytes)
    }

    pub proof fn lemma_valid_implies_recover_successful(self)
        requires
            self.valid(),
        ensures
            Self::recover(self@.durable_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                         state: self@.durable_state }),
    {
    }

    pub open spec fn recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
    {
        &&& Self::recover(state1) matches Some(j1)
        &&& Self::recover(state2) matches Some(j2)
        &&& j1.constants == j2.constants
        &&& opaque_subrange(j1.state, j1.constants.app_area_start as int, j1.constants.app_area_end as int)
               == opaque_subrange(j2.state, j2.constants.app_area_start as int, j2.constants.app_area_end as int)
    }

    pub closed spec fn space_needed_for_journal_entries(
        max_journal_entries: u64,
        max_journaled_bytes: u64,
    ) -> int
    {
        spec_space_needed_for_journal_entries(max_journal_entries, max_journaled_bytes)
    }
    

    pub closed spec fn space_needed_for_setup(ps: JournalSetupParameters) -> int
        recommends
            ps.valid(),
    {
        spec_space_needed_for_setup(ps)
    }

    pub closed spec fn ready_for_app_setup(
        bytes: Seq<u8>,
        constants: JournalConstants,
    ) -> bool
    {
        spec_ready_for_app_setup(bytes, constants)
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
            Some(addrs) => Some(addrs.min_app_area_end),
            None => None
        }
    }

    pub exec fn begin_setup(
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
                    &&& Self::recover(pm@.read_state) == Some(RecoveredJournal{ constants, state: pm@.read_state })
                    &&& constants.app_version_number == ps.app_version_number
                    &&& constants.app_program_guid == ps.app_program_guid
                    &&& constants.journal_capacity
                           >= Self::space_needed_for_journal_entries(ps.max_journal_entries, ps.max_journaled_bytes)
                    &&& opaque_aligned(constants.app_area_start as int, ps.app_area_alignment as int)
                    &&& constants.app_area_end >= constants.app_area_start + ps.app_area_size
                    &&& constants.app_area_end == pm@.len()
                    &&& Self::ready_for_app_setup(pm@.read_state, constants)
                },
                Err(JournalError::InvalidAlignment) => !ps.valid(),
                Err(JournalError::NotEnoughSpace) => ps.valid() && Self::space_needed_for_setup(*ps) > pm@.len(),
                Err(_) => false,
            }
    {
        if ps.app_area_alignment == 0 {
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
    
        if addrs.min_app_area_end > pm_size {
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
            app_area_start: addrs.app_area_start,
            app_area_end: pm_size,
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
            app_area_start: addrs.app_area_start,
            app_area_end: pm_size,
        };
    
        Ok(journal_constants)
    }

    pub exec fn end_setup(
        pm: &mut PM,
        journal_constants: &JournalConstants,
        Ghost(state_after_begin_setup): Ghost<Seq<u8>>, // the state after calling `begin_setup` and
                                                        // before initializing the application state
    )
        where
            PM: PersistentMemoryRegion
        requires
            old(pm).inv(),
            Self::ready_for_app_setup(state_after_begin_setup, *journal_constants),
            old(pm)@.len() == state_after_begin_setup.len(),
            opaque_subrange(state_after_begin_setup, 0, journal_constants.app_area_start as int)
                == opaque_subrange(old(pm)@.read_state, 0, journal_constants.app_area_start as int),
        ensures
            pm.inv(),
            pm@.flush_predicted(),
            Self::recover(pm@.durable_state) ==
                Some(RecoveredJournal{ constants: *journal_constants, state: old(pm)@.read_state }),
    {
        pm.flush();
        proof {
            lemma_auto_opaque_subrange_subrange(state_after_begin_setup, 0, journal_constants.app_area_start as int);
            lemma_auto_opaque_subrange_subrange(pm@.read_state, 0, journal_constants.app_area_start as int);
        }
    }

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<Self, JournalError>)
        requires
            wrpm.inv(),
            Self::recover(wrpm@.durable_state).is_some(),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, wrpm@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            match result {
                Ok(j) => {
                    &&& j.valid()
                    &&& j@.constants == Self::recover(wrpm@.durable_state).unwrap().constants
                    &&& j@.remaining_capacity == j@.constants.journal_capacity
                    &&& j@.journaled_addrs.is_empty()
                    &&& j@.durable_state == j@.read_state
                    &&& j@.read_state == j@.commit_state
                    &&& Self::recovery_equivalent_for_app(j@.durable_state, wrpm@.durable_state)
                },
                Err(JournalError::CRCError) => !wrpm.constants().impervious_to_corruption(),
                _ => true,
            }
    {
        let ghost old_durable_state = wrpm@.durable_state;
        let mut wrpm = wrpm;
        wrpm.flush();

        let pm = wrpm.get_pm_region_ref();
        let pm_size = pm.get_region_size(); // This establishes that `pm@.len() <= u64::MAX`
 
        let vm = Self::read_version_metadata(pm).ok_or(JournalError::CRCError)?;
        let sm = Self::read_static_metadata(pm, &vm).ok_or(JournalError::CRCError)?;
        let cdb = Self::read_committed_cdb(pm, &vm, &sm).ok_or(JournalError::CRCError)?;
        let constants = JournalConstants {
            app_version_number: sm.app_version_number,
            app_program_guid: sm.app_program_guid,
            journal_capacity: sm.journal_entries_end - sm.journal_entries_start,
            app_area_start: sm.app_area_start,
            app_area_end: sm.app_area_end,
        };
        if cdb {
            let journal_length = Self::read_journal_length(pm, Ghost(vm), &sm).ok_or(JournalError::CRCError)?;
            let entries_bytes =
                Self::read_journal_entries_bytes(pm, Ghost(vm), &sm, journal_length).ok_or(JournalError::CRCError)?;
            let ghost entries = parse_journal_entries(entries_bytes@, 0).unwrap();
            Self::install_journal_entries(&mut wrpm, Tracked(perm), Ghost(vm), &sm, &entries_bytes, Ghost(entries));
            Self::clear_log(&mut wrpm, Tracked(perm), Ghost(vm), &sm);
        }
        Ok(Self {
            wrpm,
            vm: Ghost(vm),
            sm,
            status: JournalStatus::Quiescent,
            constants,
            commit_state: Ghost(wrpm@.read_state),
            journal_length: 0,
            journaled_addrs: Ghost(Set::<int>::empty()),
            entries: Ghost(Seq::<JournalEntry>::empty()),
        })
    }
}

}
