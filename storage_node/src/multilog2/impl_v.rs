use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

pub struct UntrustedLogImpl {
    state: Ghost<MultilogView>,
}

impl UntrustedLogImpl
{
    // This static function specifies how multiple regions'
    // contents should be viewed upon recovery as an abstract
    // log state.
    pub closed spec fn recover(mem: Seq<u8>) -> Option<RecoveredMultilogState>
    {
        recover_state(mem)
    }

    pub closed spec fn inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
    {
        &&& powerpm_region.inv()
        &&& Self::recover(powerpm_region@.durable_state) == Some(self@.recover())
    }

    pub proof fn lemma_inv_implies_powerpm_inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        log_id: u128
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region)
        ensures
            powerpm_region.inv()
    {}

    pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        log_id: u128
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region),
        ensures
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
    {}

    // This function specifies how to view the in-memory state of
    // `self` as an abstract log state.
    pub closed spec fn view(&self) -> MultilogView
    {
        self.state@
    }

    pub closed spec fn spec_space_needed_for_setup(capacities: Seq<u64>) -> nat
    {
        0
    }

    // The `setup` method sets up persistent memory objects `pm_region`
    // to store an initial empty log. It returns the capacity of the log.
    // See `README.md` for more documentation.
    pub exec fn setup<PMRegion>(
        pm_region: &mut PMRegion,
        log_id: u128,
        capacities: Vec<u64>,
    ) -> (result: Result<(), MultilogErr>)
        where
            PMRegion: PersistentMemoryRegion
        requires
            old(pm_region).inv(),
            old(pm_region)@.valid(),
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            match result {
                Ok(()) => {
                    let state = RecoveredMultilogState::initialize(log_id, capacities@);
                    &&& pm_region@.len() == old(pm_region)@.len()
                    &&& pm_region@.flush_predicted()
                    &&& Self::recover(pm_region@.durable_state) == Some(state)
                },
                Err(MultilogErr::InsufficientSpaceForSetup { required_space }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& pm_region@.len() < required_space
                    &&& required_space == Self::spec_space_needed_for_setup(capacities@)
                },
                _ => false
            }
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    // The `start` static method creates an
    // `UntrustedLogImpl` out of a set of persistent memory
    // regions. It's assumed that those regions were initialized
    // with `setup` and then only `UntrustedLogImpl` methods
    // were allowed to mutate them. See `README.md` for more
    // documentation and an example of its use.
    //
    // This method is passed a write-restricted collection of
    // persistent memory regions `powerpm_region`. This restricts
    // how we can write `powerpm_region`. This is moot, though,
    // because we don't ever write to the memory.
    pub exec fn start<Perm, PMRegion>(
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128,
        Tracked(perm): Tracked<&Perm>,
        Ghost(state): Ghost<RecoveredMultilogState>,
    ) -> (result: Result<Self, MultilogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            old(powerpm_region).inv(),
            old(powerpm_region)@.valid(),
            old(powerpm_region)@.flush_predicted(),
            Self::recover(old(powerpm_region)@.durable_state) == Some(state),
            forall |s| #[trigger] perm.check_permission(s) <== Self::recover(s) == Some(state),
        ensures
            powerpm_region.inv(),
            powerpm_region.constants() == old(powerpm_region).constants(),
            match result {
                Ok(log_impl) => {
                    &&& log_impl.inv(powerpm_region)
                    &&& log_impl@.c.id == multilog_id
                    &&& log_impl@.recover() == state
                    &&& log_impl@.tentative == log_impl@.durable
                    &&& Self::recover(powerpm_region@.durable_state) == Some(state)
                },
                Err(MultilogErr::StartFailedDueToMultilogIDMismatch{ multilog_id_expected, multilog_id_read }) => {
                    &&& multilog_id_expected == multilog_id
                    &&& multilog_id_read == state.c.id
                },
                Err(MultilogErr::CRCMismatch) => !powerpm_region.constants().impervious_to_corruption(),
                _ => false,
            }
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }
    
    // The `tentatively_append` method tentatively appends
    // `bytes_to_append` to the end of the log. It's tentative in
    // that crashes will undo the appends, and reads aren't
    // allowed in the tentative part of the log. See `README.md` for
    // more documentation and examples of its use.
    //
    // This method is passed a write-restricted persistent memory
    // region `powerpm_region`. This restricts how it can write
    // `powerpm_region`. It's only given permission (in `perm`) to
    // write if it can prove that any crash after initiating the
    // write is safe. That is, any such crash must put the memory
    // in a state that recovers as the current abstract state with
    // all pending appends dropped.
    pub exec fn tentatively_append<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        which_log: u32,
        bytes_to_append: &[u8],
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<u128, MultilogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            old(self).inv(&*old(powerpm_region)),
            forall |s| #[trigger] perm.check_permission(s) <==
                Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            match result {
                Ok(offset) => {
                    &&& which_log < self@.tentative.num_logs()
                    &&& offset == old(self)@.tentative[which_log as int].tail()
                    &&& self@ == MultilogView{ tentative: old(self)@.tentative.append(which_log as int, bytes_to_append@), ..self@ }
                },
                Err(MultilogErr::InvalidLogIndex) => {
                    &&& self@ == old(self)@
                    &&& which_log >= self@.tentative.num_logs()
                },
                Err(MultilogErr::InsufficientSpaceForAppend { available_space }) => {
                    &&& self@ == old(self)@
                    &&& which_log < self@.tentative.num_logs()
                    &&& available_space < bytes_to_append@.len()
                    &&& {
                           let capacity = self@.c.capacities[which_log as int];
                           let state = self@.tentative[which_log as int];
                           ||| available_space == capacity - state.log.len()
                           ||| available_space == u128::MAX - state.head - state.log.len()
                       }
                },
                _ => false
            },
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn tentatively_advance_head<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        which_log: u32,
        new_head: u128,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            old(self).inv(&*old(powerpm_region)),
            forall |s| #[trigger] perm.check_permission(s) <==
                Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            match result {
                Ok(()) => {
                    let state = old(self)@.tentative[which_log as int];
                    &&& which_log < self@.tentative.num_logs()
                    &&& state.head <= new_head <= state.head + state.log.len()
                    &&& self@ == MultilogView{ tentative: old(self)@.tentative.advance_head(which_log as int, new_head as int), ..self@ }
                },
                Err(MultilogErr::InvalidLogIndex) => {
                    &&& self@ == old(self)@
                    &&& which_log >= self@.tentative.num_logs()
                },
                Err(MultilogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                    &&& self@ == old(self)@
                    &&& which_log < self@.tentative.num_logs()
                    &&& head == self@.tentative[which_log as int].head
                    &&& new_head < head
                },
                Err(MultilogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                    &&& self@ == old(self)@
                    &&& which_log < self@.tentative.num_logs()
                    &&& tail == self@.tentative[which_log as int].tail()
                    &&& new_head > tail
                },
                _ => false
            },
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn abort<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            old(self).inv(&*old(powerpm_region)),
            forall |s| #[trigger] perm.check_permission(s) <==
                Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            result is Ok,
            self@ == old(self)@.abort(),
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn commit<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>)
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion,
        requires
            old(self).inv(&*old(powerpm_region)),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::recover(s) == Some(old(self)@.recover())
                ||| Self::recover(s) == Some(old(self)@.commit().recover())
            },
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            result is Ok,
            self@ == old(self)@.commit(),
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

}

}
