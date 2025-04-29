#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::tokens::frac::*;
use crate::common::subrange_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;
use super::entry_v::*;
use super::inv_v::*;
use super::recover_v::*;
use super::spec_v::*;

verus! {

pub struct Journal<PM>
where
    PM: PersistentMemoryRegion,
{
    pub(super) powerpm: PoWERPersistentMemoryRegion<PM>,
    pub(super) vm: Ghost<JournalVersionMetadata>,
    pub(super) sm: JournalStaticMetadata,
    pub(super) status: Ghost<JournalStatus>,
    pub(super) constants: JournalConstants,
    pub(super) journal_length: u64,
    pub(super) journaled_addrs: Ghost<Set<int>>,
    pub(super) entries: ConcreteJournalEntries,
}

impl <PM> Journal<PM>
where
    PM: PersistentMemoryRegion,
{
    pub open(super) spec fn view(&self) -> JournalView
    {
        JournalView{
            constants: self.constants,
            pm_constants: self.powerpm.constants(),
            durable_state: self.powerpm@.durable_state,
            read_state: self.powerpm@.read_state,
            commit_state: apply_journal_entries(self.powerpm@.read_state, self.entries@, self.sm).unwrap(),
            remaining_capacity: self.constants.journal_capacity - self.journal_length,
            journaled_addrs: self.journaled_addrs@,
            powerpm_id: self.powerpm.id(),
        }
    }

    pub open(super) spec fn valid(self) -> bool
    {
        &&& self.inv()
        &&& self.status@ is Quiescent
    }

    pub open(super) spec fn recover(bytes: Seq<u8>) -> Option<RecoveredJournal>
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

    #[inline(always)]
    #[verifier::atomic]
    pub exec fn agree(&self, Tracked(r): Tracked<&GhostVar<Seq<u8>>>)
        requires
            self.valid(),
            self@.powerpm_id == r.id(),
        ensures
            self@.durable_state == r@,
        opens_invariants
            none
        no_unwind
    {
        self.powerpm.agree(Tracked(r));
    }

    pub exec fn remaining_capacity(&self) -> (result: u64)
        requires
            self.valid(),
        ensures
            result == self@.remaining_capacity,
    {
        self.constants.journal_capacity - self.journal_length
    }

    pub proof fn lemma_valid_implications(self)
        requires
            self.valid(),
        ensures
            self.recover_idempotent(),
            self@.valid(),
    {
    }

    pub exec fn journal_entry_overhead() -> (result: u64)
        ensures
            result == spec_journal_entry_overhead(),
            result <= 100,
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
            self.powerpm.lemma_inv_implies_view_valid();
        }
        self.powerpm.get_pm_region_ref()
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
        self.powerpm.flush();
    }
}

pub open(super) spec fn spec_journal_entry_overhead() -> nat
{
    (u64::spec_size_of() + u64::spec_size_of()) as nat
}

}

