use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::common::align_v::*;
use crate::pmem::wrpm_t::*;
use super::entry_v::*;
use super::layout_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::util_v::*;
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
    pub(super) entries: ConcreteJournalEntries,
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
            pm_constants: self.wrpm.constants(),
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

    pub open spec fn recover_successful(self) -> bool
    {
        Self::recover(self@.durable_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                     state: self@.durable_state })
    }

    pub proof fn lemma_valid_implies_recover_successful(self)
        requires
            self.valid(),
        ensures
            self.recover_successful(),
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
                    &&& j@.pm_constants == wrpm.constants()
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
            entries: ConcreteJournalEntries::new(),
        })
    }

    pub open spec fn write_preconditions(self, addr: u64, bytes_to_write: Seq<u8>, perm: Perm) -> bool
    {
        &&& self.valid()
        &&& self@.constants.app_area_start <= addr
        &&& addr + bytes_to_write.len() <= self@.constants.app_area_end
        &&& forall|s: Seq<u8>| {
            &&& opaque_match_except_in_range(s, self@.durable_state, addr as int, addr + bytes_to_write.len())
            &&& Self::recover(s) matches Some(j)
            &&& j.constants == self@.constants
            &&& j.state == s
        } ==> #[trigger] perm.check_permission(s)
        &&& forall|i: int| #![trigger self@.journaled_addrs.contains(i)]
            addr <= i < addr + bytes_to_write.len() ==> !self@.journaled_addrs.contains(i)
    }

    pub open spec fn write_postconditions(self, old_self: Self, addr: u64, bytes_to_write: Seq<u8>) -> bool
    {
        &&& self.valid()
        &&& self.recover_successful()
        &&& self@ == (JournalView{
                read_state: opaque_update_bytes(old_self@.read_state, addr as int, bytes_to_write),
                commit_state: opaque_update_bytes(old_self@.commit_state, addr as int, bytes_to_write),
                durable_state: self@.durable_state,
                ..old_self@
            })
        &&& opaque_match_except_in_range(self@.durable_state, old_self@.durable_state, addr as int,
                                       addr + bytes_to_write.len())
    }

    pub exec fn write_slice(
        &mut self,
        addr: u64,
        bytes_to_write: &[u8],
        Tracked(perm): Tracked<&Perm>,
    )
        requires
            old(self).write_preconditions(addr, bytes_to_write@, *perm),
        ensures
            self.write_postconditions(*old(self), addr, bytes_to_write@),
    {
        proof {
            lemma_auto_can_result_from_partial_write_effect_on_opaque();
            lemma_auto_can_result_from_write_effect_on_read_state();
            assert forall|s| can_result_from_partial_write(s, self.wrpm@.durable_state, addr as int, bytes_to_write@)
                implies #[trigger] perm.check_permission(s) by {
                assert(opaque_match_except_in_range(s, self.wrpm@.durable_state, addr as int,
                                                    addr + bytes_to_write@.len()));
                lemma_auto_opaque_subrange_subrange(s, 0, addr as int);
                lemma_auto_opaque_subrange_subrange(self.wrpm@.durable_state, 0, addr as int);
            }
        }
        self.wrpm.write(addr, bytes_to_write, Tracked(perm));
        reveal(opaque_update_bytes);
        proof {
            lemma_auto_opaque_subrange_subrange(self.wrpm@.durable_state, 0, addr as int);
            lemma_auto_opaque_subrange_subrange(old(self).wrpm@.durable_state, 0, addr as int);
        }
        self.commit_state = Ghost(opaque_update_bytes(self.commit_state@, addr as int, bytes_to_write@));
        assert(apply_journal_entries(self.wrpm@.read_state, self.entries@, 0, self.sm) == Some(self@.commit_state)) by {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(self).wrpm@.read_state, self.entries@,
                                                                       0, self.sm);
            assert forall|i: int| #![trigger self.journaled_addrs@.contains(i)]
                addr <= i < addr + bytes_to_write@.len() implies !self.journaled_addrs@.contains(i) by {
                assert(self.journaled_addrs@.contains(i) <==> old(self)@.journaled_addrs.contains(i)); // trigger
            }
            lemma_apply_journal_entries_commutes_with_update_bytes(
                old(self).wrpm@.read_state, self.entries@, self.journaled_addrs@, 0, addr as int,
                bytes_to_write@, self.sm
            );
        }
    }

    pub exec fn write_vec(
        &mut self,
        addr: u64,
        bytes_to_write: Vec<u8>,
        Tracked(perm): Tracked<&Perm>,
    )
        requires
            old(self).write_preconditions(addr, bytes_to_write@, *perm),
        ensures
            self.write_postconditions(*old(self), addr, bytes_to_write@),
    {
        self.write_slice(addr, bytes_to_write.as_slice(), Tracked(perm))
    }

    pub exec fn write_object<S>(
        &mut self,
        addr: u64,
        object: &S,
        Tracked(perm): Tracked<&Perm>,
    )
        where
            S: PmCopy,
        requires
            old(self).write_preconditions(addr, object.spec_to_bytes(), *perm),
        ensures
            self.write_postconditions(*old(self), addr, object.spec_to_bytes()),
    {
        broadcast use pmcopy_axioms;
        self.write_slice(addr, object.as_byte_slice(), Tracked(perm))
    }

    pub exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
        where 
            S: PmCopy + Sized,
        requires
            self.valid(),
            addr + S::spec_size_of() <= self@.read_state.len(),
            // We must have previously written a serialized S to this addr
            S::bytes_parseable(self@.read_state.subrange(addr as int, addr + S::spec_size_of()))
        ensures
            match bytes {
                Ok(bytes) => bytes_read_from_storage(
                    bytes@,
                    opaque_subrange(self@.read_state, addr as int, addr + S::spec_size_of()),
                    addr as int,
                    self@.pm_constants
                ),
                _ => false,
            }
    {
        reveal(opaque_subrange);
        self.wrpm.get_pm_region_ref().read_aligned(addr)
    }

    pub exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
        requires 
            self.valid(),
            addr + num_bytes <= self@.read_state.len(),
        ensures 
            match bytes {
                Ok(bytes) => bytes_read_from_storage(
                    bytes@,
                    opaque_subrange(self@.read_state, addr as int, addr + num_bytes as nat),
                    addr as int,
                    self@.pm_constants
                ),
                _ => false,
            }
    {
        reveal(opaque_subrange);
        self.wrpm.get_pm_region_ref().read_unaligned(addr, num_bytes)
    }

    pub exec fn abort(&mut self)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == (JournalView{
                commit_state: self@.read_state,
                remaining_capacity: self@.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..old(self)@
            }),
    {
        self.commit_state = Ghost(self@.read_state);
        self.journal_length = 0;
        self.journaled_addrs = Ghost(Set::<int>::empty());
        self.entries = ConcreteJournalEntries::new();
    }
}

}
