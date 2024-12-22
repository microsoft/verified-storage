use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::pmem::wrpm_t::*;
use super::layout_v::*;
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
    spec fn journal_entries_matches(self, read_state: Seq<u8>) -> bool
    {
        &&& 0 <= self.sm.journal_entries_start
        &&& self.sm.journal_entries_start + self.constants.journal_capacity <= self.sm.journal_entries_end
        &&& recover_journal_entries(read_state, self.sm, self.journal_length) == Some(self.entries@)
    }

    spec fn inv_journaled_addrs_complete(self) -> bool
    {
        forall|entry, addr| #![trigger self.entries@.contains(entry), self.journaled_addrs@.contains(addr)]
            self.entries@.contains(entry) && entry.start <= addr < entry.end() ==>
            self.journaled_addrs@.contains(addr)
    }

    spec fn inv_constants_match(self) -> bool
    {
        &&& self.constants.app_version_number == self.sm.app_version_number
        &&& self.constants.app_program_guid == self.sm.app_program_guid
        &&& self.constants.journal_capacity == self.sm.journal_entries_end - self.sm.journal_entries_start
        &&& self.constants.app_static_area_start == self.sm.app_static_area_start
        &&& self.constants.app_static_area_end == self.sm.app_static_area_end
        &&& self.constants.app_dynamic_area_start == self.sm.app_dynamic_area_start
        &&& self.constants.app_dynamic_area_end == self.sm.app_dynamic_area_end
    }

    spec fn inv(self) -> bool
    {
        let pmv = self.wrpm.view();
        &&& self.wrpm.inv()
        &&& self.inv_constants_match()
        &&& recover_version_metadata(pmv.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(pmv.durable_state, self.vm@) == Some(self.sm)
        &&& recover_committed_cdb(pmv.durable_state, self.sm) matches Some(committed)
        &&& self.status is Quiescent ==> !committed
        &&& apply_journal_entries(pmv.read_state, self.entries@, 0, self.sm) == Some(self@.commit_state)
        &&& self.inv_journaled_addrs_complete()
    }

    spec fn valid_internal(self) -> bool
    {
        &&& self.inv()
        &&& self.status is Quiescent
    }

    pub closed spec fn valid(self) -> bool
    {
        self.valid_internal()
    }

    pub proof fn lemma_valid_implies_recover_successful(self)
        requires
            self.valid(),
        ensures
            recover_journal(self@.durable_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                           state: self@.durable_state }),
    {
        reveal(recover_journal);
    }

    pub open spec fn recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
    {
        &&& recover_journal(state1) matches Some(j1)
        &&& recover_journal(state2) matches Some(j2)
        &&& j1.constants == j2.constants
        &&& opaque_subrange(j1.state, j1.constants.app_static_area_start as int, j1.constants.app_dynamic_area_end as int)
                == opaque_subrange(j2.state, j2.constants.app_static_area_start as int, j2.constants.app_dynamic_area_end as int)
    }

    pub exec fn start(
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        Tracked(perm): Tracked<&Perm>
    ) -> (result: Result<Self, JournalError>)
        requires
            wrpm.inv(),
            recover_journal(wrpm.view().read_state).is_some(),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, wrpm.view().durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            match result {
                Ok(j) => {
                    &&& j.valid()
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
 
        reveal(recover_journal);
        let vm = Self::read_version_metadata(pm).ok_or(JournalError::CRCError)?;
        let sm = Self::read_static_metadata(pm, &vm).ok_or(JournalError::CRCError)?;
        let cdb = Self::read_committed_cdb(pm, &vm, &sm).ok_or(JournalError::CRCError)?;
        let constants = JournalConstants {
            app_version_number: sm.app_version_number,
            app_program_guid: sm.app_program_guid,
            journal_capacity: sm.journal_entries_end - sm.journal_entries_start,
            app_static_area_start: sm.app_static_area_start,
            app_static_area_end: sm.app_static_area_end,
            app_dynamic_area_start: sm.app_dynamic_area_start,
            app_dynamic_area_end: sm.app_dynamic_area_end,
        };
        let ghost app_static_area =
            opaque_subrange(pm@.read_state, sm.app_static_area_start as int, sm.app_static_area_end as int);
        let ghost app_dynamic_area =
            opaque_subrange(pm@.read_state, sm.app_dynamic_area_start as int, sm.app_dynamic_area_end as int);
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
