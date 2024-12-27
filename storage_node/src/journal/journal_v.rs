use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::common::align_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::pmem::wrpm_t::*;
use super::entry_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::start_v::*;
use deps_hack::PmCopy;

verus! {

broadcast use group_opaque_subrange, pmcopy_axioms;

pub enum JournalStatus {
    Quiescent,
    WritingJournalEntries,
}

pub struct Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub(super) wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    pub(super) vm: Ghost<JournalVersionMetadata>,
    pub(super) sm: JournalStaticMetadata,
    pub(super) status: Ghost<JournalStatus>,
    pub(super) constants: JournalConstants,
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
            commit_state: apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm).unwrap(),
            remaining_capacity: self.constants.journal_capacity - self.journal_length,
            journaled_addrs: self.journaled_addrs@,
            num_journal_entries: self.entries@.len() as int,
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

    pub closed spec fn space_needed_for_journal_entry(num_bytes: nat) -> int
    {
        spec_space_needed_for_journal_entry(num_bytes)
    }

    pub closed spec fn space_needed_for_journal_entries(
        max_journal_entries: u64,
        max_journaled_bytes: u64,
    ) -> nat
    {
        spec_space_needed_for_journal_entries(max_journal_entries, max_journaled_bytes)
    }
    

    pub closed spec fn space_needed_for_setup(ps: JournalSetupParameters) -> nat
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
                    &&& opaque_aligned(constants.app_area_start as nat, ps.app_area_alignment as nat)
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
            opaque_match_in_range(state_after_begin_setup, old(pm)@.read_state, 0, journal_constants.app_area_start as int),
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
                    &&& j@.num_journal_entries == 0
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
 
        let vm = read_version_metadata(pm).ok_or(JournalError::CRCError)?;
        let sm = read_static_metadata(pm, &vm).ok_or(JournalError::CRCError)?;
        let cdb = read_committed_cdb(pm, &vm, &sm).ok_or(JournalError::CRCError)?;
        let constants = JournalConstants {
            app_version_number: sm.app_version_number,
            app_program_guid: sm.app_program_guid,
            journal_capacity: sm.journal_entries_end - sm.journal_entries_start,
            app_area_start: sm.app_area_start,
            app_area_end: sm.app_area_end,
        };
        if cdb {
            let journal_length = read_journal_length(pm, Ghost(vm), &sm).ok_or(JournalError::CRCError)?;
            let entries_bytes =
                read_journal_entries_bytes(pm, Ghost(vm), &sm, journal_length).ok_or(JournalError::CRCError)?;
            let ghost entries = parse_journal_entries(entries_bytes@).unwrap();
            install_journal_entries(&mut wrpm, Tracked(perm), Ghost(vm), &sm, &entries_bytes, Ghost(entries));
            clear_log(&mut wrpm, Tracked(perm), Ghost(vm), &sm);
        }
        Ok(Self {
            wrpm,
            vm: Ghost(vm),
            sm,
            status: Ghost(JournalStatus::Quiescent),
            constants,
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
        assert({
            &&& apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm) == Some(self@.commit_state)
            &&& self@.commit_state == opaque_update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@)
        }) by {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(self).wrpm@.read_state, self.entries@,
                                                                       self.sm);
            assert forall|i: int| #![trigger self.journaled_addrs@.contains(i)]
                addr <= i < addr + bytes_to_write@.len() implies !self.journaled_addrs@.contains(i) by {
                assert(self.journaled_addrs@.contains(i) <==> old(self)@.journaled_addrs.contains(i)); // trigger
            }
            lemma_apply_journal_entries_commutes_with_update_bytes(
                old(self).wrpm@.read_state, self.entries@, self.journaled_addrs@, addr as int,
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
                num_journal_entries: 0,
                ..old(self)@
            }),
    {
        self.journal_length = 0;
        self.journaled_addrs = Ghost(Set::<int>::empty());
        self.entries = ConcreteJournalEntries::new();
    }

    pub exec fn journal_write(
        &mut self,
        addr: u64,
        bytes_to_write: Vec<u8>,
        Tracked(perm): Tracked<&Perm>,
    )
        requires
            old(self).valid(),
            old(self)@.constants.app_area_start <= addr,
            addr + bytes_to_write.len() <= old(self)@.constants.app_area_end,
            old(self)@.remaining_capacity >= Self::space_needed_for_journal_entry(bytes_to_write@.len()),
            old(self)@.num_journal_entries < u64::MAX,
        ensures
            self.valid(),
            self.recover_successful(),
            self@ == (JournalView{
                commit_state: opaque_update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@),
                journaled_addrs: old(self)@.journaled_addrs +
                                 Set::<int>::new(|i: int| addr <= i < addr + bytes_to_write.len()),
                remaining_capacity: old(self)@.remaining_capacity -
                    Self::space_needed_for_journal_entry(bytes_to_write@.len()),
                num_journal_entries: old(self)@.num_journal_entries + 1,
                ..old(self)@
            }),
    {
        self.journal_length = self.journal_length + (size_of::<u64>() + size_of::<u64>() + bytes_to_write.len()) as u64;
        self.journaled_addrs = Ghost(self.journaled_addrs@ +
                                     Set::<int>::new(|i: int| addr <= i < addr + bytes_to_write.len()));
        let concrete_entry = ConcreteJournalEntry::new(addr, bytes_to_write);
        self.entries.push(concrete_entry);

        assert({
            &&& apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm) == Some(self@.commit_state)
            &&& self@.commit_state == opaque_update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@)
        }) by {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(old(self).wrpm@.read_state,
                                                                       old(self).entries@, self.sm);
            lemma_effect_of_append_on_apply_journal_entries(old(self).wrpm@.read_state, old(self).entries@,
                                                            concrete_entry@, self.sm);
        }

        assert(journaled_addrs_complete(self.entries@, self.journaled_addrs@)) by {
            assert forall|entry, addr| #![trigger self.entries@.contains(entry), self.journaled_addrs@.contains(addr)]
                   self.entries@.contains(entry) && entry.start <= addr < entry.end()
                   implies self.journaled_addrs@.contains(addr) by {
                if !old(self).entries@.contains(entry) { // triggers journaled_addrs_complete(old(self).entries@, ...)
                    assert(entry == concrete_entry@);
                }
            }
        }

        assert(space_needed_for_journal_entries(self.entries@) ==
               space_needed_for_journal_entries(old(self).entries@) + concrete_entry@.space_needed()) by {
            assert(self.entries@.last() == concrete_entry@);
            assert(self.entries@.drop_last() =~= old(self).entries@);
        }

        proof {
            lemma_apply_journal_entries_some_iff_journal_entries_valid(self.wrpm@.read_state, self.entries@, self.sm);
        }
    }

    #[inline]
    exec fn write_journal_entry(
        &mut self,
        Tracked(perm): Tracked<&Perm>,
        Ghost(original_durable_state): Ghost<Seq<u8>>,
        Ghost(original_read_state): Ghost<Seq<u8>>,
        current_entry_index: usize,
        current_pos: u64,
        crc_digest: &mut CrcDigest,
    ) -> (next_pos: u64)
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            old(self).status@ is WritingJournalEntries,
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_durable_state)
                ==> #[trigger] perm.check_permission(s),
            recovers_to(original_durable_state, old(self).vm@, old(self).sm, old(self).constants),
            parse_journal_entries(
                opaque_subrange(old(self).wrpm@.read_state, old(self).sm.journal_entries_start as int, current_pos as int)
            ) == Some(old(self).entries@.take(current_entry_index as int)),
            0 <= current_entry_index < old(self).entries@.len(),
            old(self).sm.journal_entries_start <= current_pos,
            current_pos == old(self).sm.journal_entries_start +
                           space_needed_for_journal_entries(old(self).entries@.take(current_entry_index as int)),
            opaque_match_in_range(original_durable_state, old(self).wrpm@.durable_state,
                                  old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            opaque_match_in_range(original_read_state, old(self).wrpm@.read_state,
                                  old(self).sm.app_area_start as int, old(self).sm.app_area_end as int),
            old(crc_digest).bytes_in_digest() ==
                opaque_subrange(old(self).wrpm@.read_state, old(self).sm.journal_entries_start as int, current_pos as int),
        ensures
            self.inv(),
            self == (Self{
                wrpm: self.wrpm,
                ..*old(self)
            }),
            next_pos == current_pos + self.entries@[current_entry_index as int].space_needed(),
            opaque_match_in_range(original_durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            opaque_match_in_range(original_read_state, self.wrpm@.read_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            parse_journal_entries(opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                                  next_pos as int))
                == Some(self.entries@.take(current_entry_index + 1)),
            current_pos < next_pos <= self.sm.journal_entries_start + self.journal_length,
            next_pos == self.sm.journal_entries_start +
                       space_needed_for_journal_entries(self.entries@.take(current_entry_index + 1)),
            next_pos == self.sm.journal_entries_start + self.journal_length
                <==> current_entry_index == self.entries@.len() - 1,
            crc_digest.bytes_in_digest() ==
                opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int, next_pos as int),
    {
        let entry: &ConcreteJournalEntry = &self.entries.entries[current_entry_index];
        let num_bytes: u64 = entry.bytes_to_write.len() as u64;

        assert({
            &&& current_pos + entry@.space_needed() ==
                self.sm.journal_entries_start +
                space_needed_for_journal_entries(self.entries@.take(current_entry_index + 1))
            &&& 0 <= current_pos
            &&& current_pos + entry@.space_needed() <= self.sm.journal_entries_start + self.journal_length
            &&& current_pos + entry@.space_needed() == self.sm.journal_entries_start + self.journal_length <==>
                 current_entry_index == self.entries@.len() - 1
        }) by {
            lemma_space_needed_for_journal_entries_increases(self.entries@, current_entry_index as int);
            lemma_space_needed_for_journal_entries_nonnegative(self.entries@.take(current_entry_index as int));
            lemma_space_needed_for_journal_entries_monotonic(self.entries@, current_entry_index + 1,
                                                             self.entries@.len() as int);
            if current_entry_index < self.entries@.len() - 1 {
                lemma_space_needed_for_journal_entries_increases(self.entries@, current_entry_index + 1);
                lemma_space_needed_for_journal_entries_monotonic(self.entries@, current_entry_index + 1,
                                                                 current_entry_index + 2);
                lemma_space_needed_for_journal_entries_monotonic(self.entries@, current_entry_index + 2,
                                                                 self.entries@.len() as int);
            }
            assert(self.entries@ =~= self.entries@.take(self.entries@.len() as int));
            assert(entry@ == self.entries@[current_entry_index as int]);
        }

        assert(forall|s: Seq<u8>| {
            &&& recovers_to(s, self.vm@, self.sm, self.constants)
            &&& opaque_match_in_range(original_durable_state, s, self.sm.app_area_start as int, self.sm.app_area_end as int)
        } ==> #[trigger] perm.check_permission(s));
        
        // First, write the `start` field of the entry, which is the address that the entry
        // is referring to, to the next position in the journal.
    
        assert forall |s|
            #[trigger] can_result_from_partial_write(s, self.wrpm@.durable_state, current_pos as int,
                                                     entry.start.spec_to_bytes()) implies {
                &&& recovers_to(s, self.vm@, self.sm, self.constants)
                &&& opaque_match_in_range(original_durable_state, s, self.sm.app_area_start as int,
                                         self.sm.app_area_end as int)
            } by {
        }
        self.wrpm.serialize_and_write::<u64>(current_pos, &entry.start, Tracked(perm));
        crc_digest.write(&entry.start);
        assert(opaque_match_in_range(original_durable_state, self.wrpm@.durable_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int));
        assert({
            &&& opaque_match_in_range(original_read_state, self@.read_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int)
            &&& crc_digest.bytes_in_digest() ==
                  opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                  current_pos + u64::spec_size_of())
        }) by {
            lemma_concatenate_opaque_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                               current_pos as int, current_pos + u64::spec_size_of());
        }
    
        // Next, write the `num_bytes` field of the entry.
    
        let num_bytes_addr = current_pos + size_of::<u64>() as u64;
        assert forall |s|
            #[trigger] can_result_from_partial_write(s, self.wrpm@.durable_state, num_bytes_addr as int,
                                                     num_bytes.spec_to_bytes()) implies {
                &&& recovers_to(s, self.vm@, self.sm, self.constants)
                &&& opaque_match_in_range(original_durable_state, s, self.sm.app_area_start as int,
                                         self.sm.app_area_end as int)
            } by {
        }
        self.wrpm.serialize_and_write::<u64>(num_bytes_addr, &num_bytes, Tracked(perm));
        crc_digest.write(&num_bytes);
        assert(opaque_match_in_range(original_durable_state, self.wrpm@.durable_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int));
        assert({
            &&& opaque_match_in_range(original_read_state, self@.read_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int)
            &&& crc_digest.bytes_in_digest() ==
                  opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                  num_bytes_addr + u64::spec_size_of())
        }) by {
            lemma_concatenate_opaque_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                               num_bytes_addr as int, num_bytes_addr + u64::spec_size_of());
        }
    
        // Next, write the `bytes_to_write` field of the entry.
    
        let bytes_to_write_addr = num_bytes_addr + size_of::<u64>() as u64;
        assert forall |s|
            #[trigger] can_result_from_partial_write(s, self.wrpm@.durable_state, bytes_to_write_addr as int,
                                                     entry.bytes_to_write@) implies {
                &&& recovers_to(s, self.vm@, self.sm, self.constants)
                &&& opaque_match_in_range(original_durable_state, s, self.sm.app_area_start as int,
                                                self.sm.app_area_end as int)
            } by {
        }
        let bytes_to_write_as_slice = entry.bytes_to_write.as_slice();
        self.wrpm.write(bytes_to_write_addr, bytes_to_write_as_slice, Tracked(perm));
        crc_digest.write_bytes(bytes_to_write_as_slice);
        assert(opaque_match_in_range(original_durable_state, self.wrpm@.durable_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int));
        assert({
            &&& opaque_match_in_range(original_read_state, self@.read_state, self.sm.app_area_start as int,
                                     self.sm.app_area_end as int)
            &&& crc_digest.bytes_in_digest() ==
                  opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                  bytes_to_write_addr + num_bytes)
        }) by {
            lemma_concatenate_opaque_subranges(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                               bytes_to_write_addr as int, bytes_to_write_addr + num_bytes);
        }
    
        let next_pos = bytes_to_write_addr + num_bytes;
        assert(parse_journal_entries(opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                                     next_pos as int))
                == Some(self.entries@.take(current_entry_index + 1))) by {
            let old_entries_bytes = opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                                    current_pos as int);
            let new_entries_bytes = opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int,
                                                    next_pos as int);
            assert(old_entries_bytes ==
                   opaque_subrange(old(self).wrpm@.read_state, self.sm.journal_entries_start as int,
                                   current_pos as int)) by {
            }
            assert(new_entries_bytes =~= old_entries_bytes + entry.start.spec_to_bytes()
                                         + num_bytes.spec_to_bytes() + entry.bytes_to_write@) by {
                reveal(opaque_subrange);
            }
            assert(parse_journal_entries(new_entries_bytes) ==
                   Some(self.entries@.take(current_entry_index as int).push(entry@))) by {
                lemma_parse_journal_entries_append(old_entries_bytes,
                                                   self.entries@.take(current_entry_index as int), entry@);
            }
            assert(self.entries@.take(current_entry_index as int).push(entry@) =~=
                   self.entries@.take(current_entry_index + 1));
        }

        next_pos
    }

    exec fn write_journal_entries(
        &mut self,
        Tracked(perm): Tracked<&Perm>,
    ) -> (journal_entries_crc: u64)
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).valid(),
            forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, old(self).wrpm@.durable_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self == (Self{
                status: Ghost(JournalStatus::WritingJournalEntries),
                wrpm: self.wrpm,
                ..*old(self)
            }),
            opaque_match_in_range(old(self).wrpm@.durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            opaque_match_in_range(old(self).wrpm@.read_state, self.wrpm@.read_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
            parse_journal_entries(extract_bytes(self.wrpm@.read_state, self.sm.journal_entries_start as nat,
                                                 self.journal_length as nat))
                == Some(self.entries@),
            journal_entries_crc ==
                spec_crc_u64(extract_bytes(self.wrpm@.read_state, self.sm.journal_entries_start as nat,
                                            self.journal_length as nat)),
    {
        self.status = Ghost(JournalStatus::WritingJournalEntries);
        let mut current_entry_index: usize = 0;
        let mut current_pos = self.sm.journal_entries_start;
        let end_pos = current_pos + self.journal_length;
        let ghost original_durable_state = self.wrpm@.durable_state;
        let ghost original_read_state = self.wrpm@.read_state;
        assert(opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int, current_pos as int)
               =~= Seq::<u8>::empty()) by { reveal(opaque_subrange); }
        assert(self.entries@.take(current_entry_index as int) =~= Seq::<JournalEntry>::empty());
        let mut crc_digest = CrcDigest::new();
        proof {
            lemma_space_needed_for_journal_entries_zero_iff_journal_empty(self.entries@);
        }
        while current_pos < end_pos
            invariant
                self.inv(),
                end_pos == self.sm.journal_entries_start + self.journal_length,
                forall|s: Seq<u8>| spec_recovery_equivalent_for_app(s, original_durable_state)
                    ==> #[trigger] perm.check_permission(s),
                recovers_to(original_durable_state, self.vm@, self.sm, self.constants),
                parse_journal_entries(
                    opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int, current_pos as int)
                ) == Some(self.entries@.take(current_entry_index as int)),
                0 <= current_entry_index <= self.entries@.len(),
                self.sm.journal_entries_start <= current_pos <= end_pos,
                current_pos == end_pos <==> current_entry_index == self.entries@.len(),
                current_pos == self.sm.journal_entries_start +
                               space_needed_for_journal_entries(self.entries@.take(current_entry_index as int)),
                opaque_match_in_range(original_durable_state, self.wrpm@.durable_state,
                                  self.sm.app_area_start as int, self.sm.app_area_end as int),
                opaque_match_in_range(original_read_state, self.wrpm@.read_state,
                self.sm.app_area_start as int, self.sm.app_area_end as int),
                self == (Self{ status: Ghost(JournalStatus::WritingJournalEntries), wrpm: self.wrpm, ..*old(self) }),
                crc_digest.bytes_in_digest() ==
                    opaque_subrange(self.wrpm@.read_state, self.sm.journal_entries_start as int, current_pos as int),
        {
            current_pos = self.write_journal_entry(Tracked(perm),
                                                   Ghost(original_durable_state), Ghost(original_read_state),
                                                   current_entry_index, current_pos,
                                                   &mut crc_digest);
            current_entry_index = current_entry_index + 1;
        }
        assert(self.entries@ == self.entries@.take(current_entry_index as int));
        crc_digest.sum64()
    }

    pub exec fn commit(&mut self, Tracked(perm): Tracked<&Perm>)
        requires
            old(self).valid(),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, old(self)@.durable_state)
                ==> #[trigger] perm.check_permission(s),
            forall|s: Seq<u8>| Self::recovery_equivalent_for_app(s, old(self)@.commit_state)
                ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(),
            self@ == (JournalView{
                durable_state: old(self)@.commit_state,
                read_state: old(self)@.commit_state,
                commit_state: old(self)@.commit_state,
                remaining_capacity: self@.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..old(self)@
            }),
    {
        let journal_entries_crc = self.write_journal_entries(Tracked(perm));
        // write journal metadata (length, length CRC, entries CRC)
        // flush
        // write committed CDB
        // install log
        // clear log
        assume(false); // TODO @jay
        clear_log(&mut self.wrpm, Tracked(perm), self.vm, &self.sm);
        assume(false); // TODO @jay
    }
}

}
