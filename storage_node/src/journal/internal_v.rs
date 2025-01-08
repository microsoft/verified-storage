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
use super::entry_v::*;
use super::inv_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_v::*;
use super::start_v::*;

verus! {

pub(super) struct JournalInternal<Perm, PM>
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

impl <Perm, PM> JournalInternal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub(super) open spec fn view(&self) -> JournalView
    {
        JournalView{
            constants: self.constants,
            pm_constants: self.wrpm.constants(),
            durable_state: self.wrpm@.durable_state,
            read_state: self.wrpm@.read_state,
            commit_state: apply_journal_entries(self.wrpm@.read_state, self.entries@, self.sm).unwrap(),
            remaining_capacity: self.constants.journal_capacity - self.journal_length,
            journaled_addrs: self.journaled_addrs@,
        }
    }

    pub(super) open spec fn valid(self) -> bool
    {
        &&& self.inv()
        &&& self.status@ is Quiescent
    }

    pub(super) open spec fn recover(bytes: Seq<u8>) -> Option<RecoveredJournal>
    {
        recover_journal(bytes)
    }

    pub(super) open spec fn recover_successful(self) -> bool
    {
        Self::recover(self@.durable_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                     state: self@.durable_state })
    }

    pub(super) open spec fn recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
    {
        &&& Self::recover(state1) matches Some(j1)
        &&& Self::recover(state2) matches Some(j2)
        &&& j1.constants == j2.constants
        &&& j1.state.subrange(j1.constants.app_area_start as int, j1.constants.app_area_end as int)
               == j2.state.subrange(j2.constants.app_area_start as int, j2.constants.app_area_end as int)
    }

    pub(super) open spec fn spec_journal_entry_overhead() -> nat
    {
        (u64::spec_size_of() + u64::spec_size_of()) as nat
    }

    pub(super) exec fn journal_entry_overhead() -> (result: u64)
        ensures
            result == Self::spec_journal_entry_overhead()
    {
        broadcast use pmcopy_axioms;
        (size_of::<u64>() + size_of::<u64>()) as u64
    }

    pub(super) exec fn read_aligned<S>(&self, addr: u64) -> (bytes: Result<MaybeCorruptedBytes<S>, PmemError>)
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
        self.wrpm.get_pm_region_ref().read_aligned(addr)
    }

    pub(super) exec fn read_unaligned(&self, addr: u64, num_bytes: u64) -> (bytes: Result<Vec<u8>, PmemError>) 
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
        self.wrpm.get_pm_region_ref().read_unaligned(addr, num_bytes)
    }

    pub(super) exec fn abort(&mut self)
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
        self.journal_length = 0;
        self.journaled_addrs = Ghost(Set::<int>::empty());
        self.entries = ConcreteJournalEntries::new();
    }
}

}

