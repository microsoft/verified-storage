use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::size_of;
use crate::pmem::wrpm_t::*;
use super::commit_v::*;
use super::entry_v::*;
use super::internal_v::*;
use super::inv_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::start_v::*;
use super::write_v::*;

verus! {

pub struct Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    j: JournalInternal<Perm, PM>,
}

impl<Perm, PM> View for Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    type V = JournalView;
    
    closed spec fn view(&self) -> JournalView
    {
        self.j@
    }
}

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub closed spec fn valid(self) -> bool
    {
        self.j.valid()
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

    pub open spec fn recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
    {
        &&& Self::recover(state1) matches Some(j1)
        &&& Self::recover(state2) matches Some(j2)
        &&& j1.constants == j2.constants
        &&& j1.state.subrange(j1.constants.app_area_start as int, j1.constants.app_area_end as int)
               == j2.state.subrange(j2.constants.app_area_start as int, j2.constants.app_area_end as int)
    }

    pub closed spec fn spec_journal_entry_overhead() -> nat
    {
        JournalInternal::<Perm, PM>::spec_journal_entry_overhead()
    }

    pub exec fn journal_entry_overhead() -> (result: u64)
        ensures
            result == Self::spec_journal_entry_overhead()
    {
        JournalInternal::<Perm, PM>::journal_entry_overhead()
    }

    pub closed spec fn spec_space_needed_for_setup(journal_capacity: nat) -> nat
    {
        JournalInternal::<Perm, PM>::spec_space_needed_for_setup(journal_capacity)
    }

    pub exec fn space_needed_for_setup(journal_capacity: &OverflowingU64) -> (result: OverflowingU64)
        ensures
            result@ == Self::spec_space_needed_for_setup(journal_capacity@),
            journal_capacity@ <= result@,
    {
        JournalInternal::<Perm, PM>::space_needed_for_setup(journal_capacity)
    }

    pub exec fn setup(
        pm: &mut PM,
        jc: &JournalConstants,
    ) -> (result: Result<(), JournalError>)
        where
            PM: PersistentMemoryRegion
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
        JournalInternal::<Perm, PM>::setup(pm, jc)
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
                    &&& j@.valid()
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
        match JournalInternal::<Perm, PM>::start(wrpm, Tracked(perm)) {
            Ok(j) => Ok(Self{ j }),
            Err(e) => Err(e),
        }
    }

    pub open spec fn write_preconditions(self, addr: u64, bytes_to_write: Seq<u8>, perm: Perm) -> bool
    {
        &&& self.valid()
        &&& self@.constants.app_area_start <= addr
        &&& addr + bytes_to_write.len() <= self@.constants.app_area_end
        &&& forall|s: Seq<u8>| {
            &&& seqs_match_except_in_range(s, self@.durable_state, addr as int, addr + bytes_to_write.len())
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
        &&& self@.valid()
        &&& self.recover_successful()
        &&& self@ == (JournalView{
                read_state: update_bytes(old_self@.read_state, addr as int, bytes_to_write),
                commit_state: update_bytes(old_self@.commit_state, addr as int, bytes_to_write),
                durable_state: self@.durable_state,
                ..old_self@
            })
        &&& old_self@.matches_except_in_range(self@, addr as int, addr + bytes_to_write.len())
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
        self.j.write_slice(addr, bytes_to_write, Tracked(perm))
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
                    self@.read_state.subrange(addr as int, addr + S::spec_size_of()),
                    addr as int,
                    self@.pm_constants
                ),
                _ => false,
            }
    {
        self.j.read_aligned::<S>(addr)
    }

    pub exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
        requires 
            self.valid(),
            addr + num_bytes <= self@.read_state.len(),
        ensures 
            match bytes {
                Ok(bytes) => bytes_read_from_storage(
                    bytes@,
                    self@.read_state.subrange(addr as int, addr + num_bytes as nat),
                    addr as int,
                    self@.pm_constants
                ),
                _ => false,
            }
    {
        self.j.read_unaligned(addr, num_bytes)
    }

    pub exec fn abort(&mut self)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@.valid(),
            self.recover_successful(),
            self@ == (JournalView{
                commit_state: self@.read_state,
                remaining_capacity: self@.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..old(self)@
            }),
    {
        self.j.abort();
    }

    pub exec fn journal_write(
        &mut self,
        addr: u64,
        bytes_to_write: Vec<u8>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), JournalError>)
        requires
            old(self).valid(),
            old(self)@.constants.app_area_start <= addr,
            addr + bytes_to_write.len() <= old(self)@.constants.app_area_end,
        ensures
            self.valid(),
            self@.valid(),
            self.recover_successful(),
            ({
                let space_needed = Self::spec_journal_entry_overhead() + bytes_to_write@.len();
                match result {
                    Ok(_) => {
                        &&& space_needed <= old(self)@.remaining_capacity
                        &&& self@ == (JournalView{
                               commit_state: update_bytes(old(self)@.commit_state, addr as int, bytes_to_write@),
                               journaled_addrs: old(self)@.journaled_addrs +
                                                Set::<int>::new(|i: int| addr <= i < addr + bytes_to_write.len()),
                               remaining_capacity: old(self)@.remaining_capacity - space_needed,
                               ..old(self)@
                           })
                        &&& self@.matches_except_in_range(old(self)@, addr as int, addr + bytes_to_write.len())
                    },
                    Err(JournalError::NotEnoughSpace) => {
                        &&& space_needed > old(self)@.remaining_capacity
                        &&& self == old(self)
                    },
                    Err(_) => false,
                }
            }),
    {
        self.j.journal_write(addr, bytes_to_write, Tracked(perm))
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
            self@.valid(),
            self.recover_successful(),
            self@ == (JournalView{
                durable_state: self@.commit_state,
                read_state: self@.commit_state,
                commit_state: self@.commit_state,
                remaining_capacity: self@.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..old(self)@
            }),
            seqs_match_in_range(old(self)@.commit_state, self@.commit_state, self@.constants.app_area_start as int,
                                self@.constants.app_area_end as int),
    {
        self.j.commit(Tracked(perm))
    }
}

}
