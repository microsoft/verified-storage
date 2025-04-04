use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::frac_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;
use deps_hack::rand::Rng;
use super::impl_v::*;
use super::spec_t::*;
use vstd::invariant::*;

verus! {

// A `TrustedPermission` is the type of a tracked object
// indicating permission to update memory. It restricts updates so
// that if a crash happens, the resulting memory `mem` satisfies
// `is_state_allowable(mem)`.
//
// The struct is defined in this file, and it has a non-public
// field, so the only code that can create one is in this file.
// So untrusted code in other files can't create one, and we can
// rely on it to restrict access to persistent memory.
#[allow(dead_code)]
pub struct TrustedPermission {
    ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
}

impl CheckPermission<Seq<u8>> for TrustedPermission {
    closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
        (self.is_state_allowable)(state)
    }

    closed spec fn valid(&self, id: int) -> bool
    {
        true
    }

    proof fn apply(tracked &self, tracked credit: OpenInvariantCredit, tracked r: &mut Frac<Seq<u8>>, new_state: Seq<u8>)
    {
        assume(false);
    }
}

impl TrustedPermission {

    // This is one of two constructors for `TrustedPermission`.
    // It conveys permission to do any update as long as a
    // subsequent crash and recovery can only lead to given
    // state `state`.
    proof fn new_one_possibility(state: RecoveredMultilogState) -> (tracked perm: Self)
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==> UntrustedMultilogImpl::recover(s) == Some(state)
    {
        Self {
            is_state_allowable: |s| UntrustedMultilogImpl::recover(s) == Some(state)
        }
    }

    // This is the second of two constructors for
    // `TrustedPermission`.  It conveys permission to do any
    // update as long as a subsequent crash and recovery can only
    // lead to one of two given abstract states `state1` and
    // `state2`.
    proof fn new_two_possibilities(
        state1: RecoveredMultilogState,
        state2: RecoveredMultilogState
    ) -> (tracked perm: Self)
        ensures
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| UntrustedMultilogImpl::recover(s) == Some(state1)
                ||| UntrustedMultilogImpl::recover(s) == Some(state2)
            }
    {
        Self {
            is_state_allowable: |s| {
                ||| UntrustedMultilogImpl::recover(s) == Some(state1)
                ||| UntrustedMultilogImpl::recover(s) == Some(state2)
            }
        }
    }
}

/// A `MultilogImpl` wraps one `UntrustedMultilogImpl` and one persistent
/// memory region to provide the executable interface that turns
/// the persistent memory region into a log.
///
/// The `untrusted_multilog_impl` field is the wrapped
/// `UntrustedMultilogImpl`.
///
/// The `powerpm_region` field contains the write-restricted persistent
/// memory. This memory will only allow updates allowed by a
/// tracked `TrustedPermission`. So we can pass `powerpm_region` to an
/// untrusted method, along with a restricting
/// `TrustedPermission`, to limit what it's allowed to do.

pub struct MultilogImpl<PMRegion: PersistentMemoryRegion> {
    untrusted_multilog_impl: UntrustedMultilogImpl,
    powerpm_region: PoWERPersistentMemoryRegion<TrustedPermission, PMRegion>
}

impl <PMRegion: PersistentMemoryRegion> MultilogImpl<PMRegion> {
    // The view of a `MultilogImpl` is whatever the
    // `UntrustedMultilogImpl` it wraps says it is.
    pub closed spec fn view(self) -> MultilogView
    {
        self.untrusted_multilog_impl@
    }

    // The constants of a `MultilogImpl` are whatever the
    // persistent memory it wraps says they are.
    pub closed spec fn constants(&self) -> PersistentMemoryConstants {
        self.powerpm_region.constants()
    }

    pub closed spec fn recover(s: Seq<u8>) -> Option<RecoveredMultilogState> {
        UntrustedMultilogImpl::recover(s)
    }

    // This is the validity condition that is maintained between
    // calls to methods on `self`.
    //
    // That is, each of the trusted wrappers on untrusted methods
    // below (e.g., `commit`, `advance_head`) can count on `valid`
    // holding because it demands that each untrusted method
    // maintains it.
    //
    // One element of `valid` is that the untrusted `inv` function
    // holds.
    //
    // The other element of `valid` is that the persistent memory,
    // if it crashes and recovers, must represent the current
    // abstract state with pending tentative appends dropped.
    pub closed spec fn valid(self) -> bool {
        &&& self.untrusted_multilog_impl.inv(&self.powerpm_region)
        &&& UntrustedMultilogImpl::recover(self.powerpm_region@.durable_state) == Some(self@.recover())
    }

    pub closed spec fn spec_space_needed_for_setup(capacities: Seq<u64>) -> nat
    {
        UntrustedMultilogImpl::spec_space_needed_for_setup(capacities)
    }

    pub exec fn space_needed_for_setup(capacities: &Vec<u64>) -> (result: Result<u64, MultilogErr>)
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(capacities@),
                Err(MultilogErr::SpaceNeededForSetupExceedsMax) =>
                    Self::spec_space_needed_for_setup(capacities@) > u64::MAX,
                Err(_) => false,
            },
    {
        UntrustedMultilogImpl::space_needed_for_setup(capacities)
    }

    // The `setup` method sets up persistent memory regions
    // `pm_region` to store an initial empty log. It returns a
    // vector listing the capacity of the log as well as a
    // fresh log ID to uniquely identify it. See `README.md`
    // for more documentation.
    pub exec fn setup(
        pm_region: &mut PMRegion,
        multilog_id: u128,
        capacities: Vec<u64>,
    ) -> (result: Result<(), MultilogErr>)
        requires
            old(pm_region).inv(),
            old(pm_region)@.valid(),
        ensures
            pm_region.inv(),
            pm_region@.valid(),
            match result {
                Ok(()) => {
                    let state = RecoveredMultilogState::initialize(multilog_id, capacities@);
                    &&& pm_region@.len() == old(pm_region)@.len()
                    &&& pm_region@.flush_predicted()
                    &&& Self::recover(pm_region@.durable_state) == Some(state)
                },
                Err(MultilogErr::SpaceNeededForSetupExceedsMax) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& Self::spec_space_needed_for_setup(capacities@) > u64::MAX
                },
                Err(MultilogErr::InsufficientSpaceForSetup { required_space }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& pm_region@.len() < required_space
                    &&& required_space == Self::spec_space_needed_for_setup(capacities@)
                },
                _ => false
            }
    {
        UntrustedMultilogImpl::setup(pm_region, multilog_id, capacities)
    }

    // The `start` method creates an `UntrustedMultilogImpl` out of a
    // persistent memory region. It's assumed that the region was
    // initialized with `setup` and then only log operations were
    // allowed to mutate them. See `README.md` for more
    // documentation and an example of use.
    pub exec fn start(pm_region: PMRegion, multilog_id: u128) -> (result: Result<Self, MultilogErr>)
        requires
            pm_region.inv(),
            pm_region@.valid(),
            pm_region@.read_state == pm_region@.durable_state,
            UntrustedMultilogImpl::recover(pm_region@.durable_state).is_Some(),
        ensures
            match result {
                Ok(trusted_log_impl) => {
                    &&& trusted_log_impl.valid()
                    &&& trusted_log_impl.constants() == pm_region.constants()
                    &&& trusted_log_impl@.c.id == multilog_id
                    &&& trusted_log_impl@.tentative == trusted_log_impl@.durable
                    &&& Self::recover(pm_region@.durable_state) == Some(trusted_log_impl@.recover())
                },
                Err(MultilogErr::StartFailedDueToMultilogIDMismatch{ multilog_id_expected, multilog_id_read }) => {
                    &&& multilog_id_expected == multilog_id
                    &&& multilog_id_read == Self::recover(pm_region@.durable_state).unwrap().c.id
                },
                Err(MultilogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption(),
                _ => false,
            }
    {
        // We allow the untrusted `start` method to update memory
        // as part of its initialization. But, to avoid bugs
        // stemming from crashes in the middle of this routine, we
        // must restrict how it updates memory. We must only let
        // it write such that, if a crash happens in the middle,
        // it doesn't change the persistent state.

        let ghost state = UntrustedMultilogImpl::recover(pm_region@.durable_state).unwrap();
        let (mut powerpm_region, _) = PoWERPersistentMemoryRegion::<TrustedPermission, PMRegion>::new(pm_region);
        let tracked perm = TrustedPermission::new_one_possibility(state);
        let untrusted_multilog_impl =
            UntrustedMultilogImpl::start::<TrustedPermission, PMRegion>(&mut powerpm_region, multilog_id, Tracked(&perm), Ghost(state))?;
        Ok(
            MultilogImpl {
                untrusted_multilog_impl,
                powerpm_region
            },
        )
    }

    // The `tentatively_append` method tentatively appends
    // `bytes_to_append` to the end of the log. It's tentative in
    // that crashes will undo the appends, and reads aren't
    // allowed in the tentative part of the log. See `README.md` for
    // more documentation and examples of use.
    pub exec fn tentatively_append(&mut self, which_log: u32, bytes_to_append: &[u8])
                                   -> (result: Result<u128, MultilogErr>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self.constants() == old(self).constants(),
            match result {
                Ok(offset) => {
                    &&& which_log < old(self)@.tentative.num_logs()
                    &&& offset == old(self)@.tentative[which_log as int].tail()
                    &&& self@ == MultilogView{ tentative: old(self)@.tentative.append(which_log as int, bytes_to_append@),
                                              ..self@ }
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
            }
    {
        // For crash safety, we must restrict the untrusted code's
        // writes to persistent memory. We must only let it write
        // such that, if a crash happens in the middle of a write,
        // the view of the persistent state is the current
        // state with pending appends dropped.
        let tracked perm = TrustedPermission::new_one_possibility(self@.recover());
        self.untrusted_multilog_impl.tentatively_append(&mut self.powerpm_region, which_log, bytes_to_append,
                                                        Tracked(&perm))
    }

    pub exec fn tentatively_advance_head(&mut self, which_log: u32, new_head: u128) -> (result: Result<(), MultilogErr>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self.constants() == old(self).constants(),
            match result {
                Ok(()) => {
                    let state = old(self)@.tentative[which_log as int];
                    &&& which_log < old(self)@.tentative.num_logs()
                    &&& state.head <= new_head <= state.head + state.log.len()
                    &&& self@ == MultilogView{ tentative: old(self)@.tentative.advance_head(which_log as int,
                                                                                         new_head as int), ..self@ }
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
            }
    {
        // For crash safety, we must restrict the untrusted code's
        // writes to persistent memory. We must only let it write
        // such that, if a crash happens in the middle of a write,
        // the view of the persistent state is the current
        // state with pending appends dropped.
        let tracked perm = TrustedPermission::new_one_possibility(self@.recover());
        self.untrusted_multilog_impl.tentatively_advance_head(&mut self.powerpm_region, which_log, new_head,
                                                              Tracked(&perm))
    }

    pub exec fn abort(&mut self) -> (result: Result<(), MultilogErr>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self.constants() == old(self).constants(),
            result is Ok,
            self@ == old(self)@.abort(),
    {
        // For crash safety, we must restrict the untrusted code's
        // writes to persistent memory. We must only let it write
        // such that, if a crash happens in the middle of a write,
        // the view of the persistent state is the current
        // state with pending appends dropped.
        let tracked perm = TrustedPermission::new_one_possibility(self@.recover());
        self.untrusted_multilog_impl.abort(&mut self.powerpm_region, Tracked(&perm))
    }

    // The `commit` method atomically commits all tentative
    // appends that have been done to `self` since the last
    // commit. The commit is atomic in that even if there's a
    // crash in the middle, the recovered-to state either reflects
    // all those tentative appends or none of them. See `README.md`
    // for more documentation and examples of use.
    pub exec fn commit(&mut self) -> (result: Result<(), MultilogErr>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self.constants() == old(self).constants(),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                _ => false
            }
    {
        // For crash safety, we must restrict the untrusted code's
        // writes to persistent memory. We must only let it write
        // such that, if a crash happens in the middle of a write,
        // the view of the persistent state is either the current
        // state with all pending appends dropped or the current
        // state with all uncommitted appends committed.
        let tracked perm = TrustedPermission::new_two_possibilities(self@.recover(), self@.commit().recover());
        self.untrusted_multilog_impl.commit(&mut self.powerpm_region, Tracked(&perm))
    }

    // The `read` method reads `len` bytes from the multilog starting
    // at virtual position `pos`. It isn't allowed to read earlier
    // than the head or past the committed tail. See `README.md` for
    // more documentation and examples of use.
    pub exec fn read(&self, which_log: u32, pos: u128, len: u64) -> (result: Result<Vec<u8>, MultilogErr>)
        requires
            self.valid(),
            pos + len <= u128::MAX,
        ensures
            ({
                let log = self@.tentative[which_log as int];
                match result {
                    Ok(bytes) => {
                        let true_bytes = self@.tentative.read(which_log as int, pos as int, len as int);
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos >= log.head
                        &&& pos + len <= log.tail()
                        &&& read_correct_modulo_corruption(bytes@, true_bytes, self.constants())
                    },
                    Err(MultilogErr::InvalidLogIndex) => {
                        which_log >= self@.tentative.num_logs()
                    },
                    Err(MultilogErr::CantReadBeforeHead{ head: head_pos }) => {
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos < log.head
                        &&& head_pos == log.head
                    },
                    Err(MultilogErr::CantReadPastTail{ tail }) => {
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos + len > log.tail()
                        &&& tail == log.tail()
                    },
                    _ => false,
                }
            })
    {
        self.untrusted_multilog_impl.read(&self.powerpm_region, which_log, pos, len)
    }

    pub exec fn get_num_logs(&self) -> (result: Result<u32, MultilogErr>)
        requires
            self.valid()
        ensures
            result is Ok,
            result.unwrap() == self@.tentative.num_logs(),
    {
        self.untrusted_multilog_impl.get_num_logs(&self.powerpm_region)
    }

    // The `get_head_tail_and_capacity` method returns three
    // pieces of metadata about the log: the virtual head
    // position, the virtual tail position, and the capacity. The
    // capacity is the maximum number of bytes there can be in the
    // log past the head, including bytes in tentative appends
    // that haven't been committed yet. See `README.md` for more
    // documentation and examples of use.
    pub exec fn get_head_tail_and_capacity(&self, which_log: u32) -> (result: Result<(u128, u128, u64), MultilogErr>)
        requires
            self.valid()
        ensures
            match result {
                Ok((result_head, result_tail, result_capacity)) => {
                    &&& result_head == self@.tentative[which_log as int].head
                    &&& result_tail == self@.tentative[which_log as int].tail()
                    &&& result_capacity == self@.c.capacities[which_log as int]
                },
                Err(MultilogErr::InvalidLogIndex) => {
                    which_log >= self@.tentative.num_logs()
                },
                _ => false
            }
    {
        self.untrusted_multilog_impl.get_head_tail_and_capacity(&self.powerpm_region, which_log)
    }

}

}
