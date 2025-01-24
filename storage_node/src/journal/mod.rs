mod commit_v;
mod entry_v;
mod inv_v;
mod recover_v;
mod setup_v;
mod spec_v;
mod start_v;
mod write_v;

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
use commit_v::*;
use entry_v::*;
use inv_v::*;
use recover_v::*;
use setup_v::*;
use spec_v::*;
use start_v::*;
use write_v::*;

verus! {

pub use spec_v::{broadcast_journal_view_matches_in_range_can_narrow_range,
                 JournalConstants, JournalError, JournalView, RecoveredJournal};

pub struct Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
    vm: Ghost<JournalVersionMetadata>,
    sm: JournalStaticMetadata,
    status: Ghost<JournalStatus>,
    constants: JournalConstants,
    journal_length: u64,
    journaled_addrs: Ghost<Set<int>>,
    entries: ConcreteJournalEntries,
}

impl <Perm, PM> Journal<Perm, PM>
    where
        PM: PersistentMemoryRegion,
        Perm: CheckPermission<Seq<u8>>,
{
    pub closed spec fn view(&self) -> JournalView
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

    pub closed spec fn valid(self) -> bool
    {
        &&& self.inv()
        &&& self.status@ is Quiescent
    }

    pub closed spec fn recover(bytes: Seq<u8>) -> Option<RecoveredJournal>
    {
        recover_journal(bytes)
    }

    pub open spec fn recover_idempotent(self) -> bool
    {
        Self::recover(self@.durable_state) == Some(RecoveredJournal{ constants: self@.constants,
                                                                     state: self@.durable_state })
    }

    pub open spec fn state_recovery_idempotent(state: Seq<u8>, constants: JournalConstants) -> bool
    {
        Self::recover(state) == Some(RecoveredJournal{ constants, state })
    }

    pub open spec fn recovery_equivalent_for_app(state1: Seq<u8>, state2: Seq<u8>) -> bool
    {
        &&& Self::recover(state1) matches Some(j1)
        &&& Self::recover(state2) matches Some(j2)
        &&& j1.state.len() == state1.len() == state2.len()
        &&& j1.constants == j2.constants
        &&& seqs_match_in_range(j1.state, j2.state, j1.constants.app_area_start as int, j1.constants.app_area_end as int)
    }

    pub proof fn lemma_valid_implications(self)
        requires
            self.valid(),
        ensures
            self.recover_idempotent(),
            self@.valid(),
    {
    }

    pub closed spec fn spec_journal_entry_overhead() -> nat
    {
        (u64::spec_size_of() + u64::spec_size_of()) as nat
    }

    pub exec fn journal_entry_overhead() -> (result: u64)
        ensures
            result == Self::spec_journal_entry_overhead()
    {
        broadcast use pmcopy_axioms;
        (size_of::<u64>() + size_of::<u64>()) as u64
    }

    pub exec fn get_pm_region_ref(&self) -> (result: &PM)
        requires
            self.valid(),
        ensures
            result.inv(),
            result.constants() == self@.pm_constants,
            result@.read_state == self@.read_state,
            result@.valid(),
    {
        proof {
            self.wrpm.lemma_inv_implies_view_valid();
        }
        self.wrpm.get_pm_region_ref()
    }

    pub exec fn constants(&self) -> (result: &JournalConstants)
        requires
            self.valid(),
        ensures
            result == self@.constants,
    {
        &self.constants
    }

    pub exec fn abort(&mut self)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@.valid(),
            self.recover_idempotent(),
            self@ == old(self)@.abort(),
    {
        self.journal_length = 0;
        self.journaled_addrs = Ghost(Set::<int>::empty());
        self.entries = ConcreteJournalEntries::new();
    }

    pub exec fn flush(&mut self)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@,
            self@.durable_state == self@.read_state,
    {
        self.wrpm.flush();
    }
}

}

