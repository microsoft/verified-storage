use std::fmt::Write;

use crate::infinitelog_t::*;
use crate::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;
use vstd::slice::*;
use crate::sccf::CheckPermission;
use crate::logimpl_v::*;

verus! {

    pub open spec fn recovery_view() -> (result: FnSpec(Seq<u8>) -> Option<AbstractInfiniteLogState>)
    {
        |c| UntrustedLogImpl::convert_from_pm_contents_to_log_state2(c)
    }

    pub open spec fn can_only_crash_as_state(pm: PersistentMemoryView, state: AbstractInfiniteLogState) -> bool
    {
        forall |s| #[trigger] pm.can_crash_as(s) ==> recovery_view()(s) == Some(state)
    }

    /// A `TrustedPermission` indicates what states of persistent
    /// memory are permitted. The struct isn't public, so it can't be
    /// created outside of this file. As a further defense against one
    /// being created outside this file, its fields aren't public, and
    /// the constructor `TrustedPermission::new` isn't public.
    
    pub struct TrustedPermission {
        ghost is_state_allowable: FnSpec(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedPermission {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedPermission {
        proof fn new(cur: AbstractInfiniteLogState,
                     next: FnSpec(AbstractInfiniteLogState, AbstractInfiniteLogState) -> bool)
                     -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    crate::sccf::is_state_allowable(cur, s, recovery_view(), next)
        {
            Self { is_state_allowable: |s| crate::sccf::is_state_allowable(cur, s, recovery_view(), next) }
        }
    }

    /// A `InfiniteLogImpl` wraps an `UntrustedLogImpl` to provide the
    /// executable interface that turns a persistent memory region
    /// into an effectively infinite log. It provides a simple
    /// interface to higher-level code.
    pub struct InfiniteLogImpl {
        untrusted_log_impl: UntrustedLogImpl,
        wrpm: WriteRestrictedPersistentMemory<TrustedPermission>,
        state: Ghost<AbstractInfiniteLogState>
    }

    pub enum InfiniteLogErr {
        InsufficientSpaceForSetup { required_space: u64 },
        CantReadBeforeHead { head: u64 },
        CantReadPastTail { tail: u64 },
        InsufficientSpaceForAppend { available_space: u64 },
        CRCMismatch,
        CantAdvanceHeadPositionBeforeHead { head: u64 },
        CantAdvanceHeadPositionBeyondTail { tail: u64 },
        InvalidHeader { head: u64, tail: u64, log_size: u64 },
    }

    impl InfiniteLogImpl {
        pub closed spec fn view(self) -> AbstractInfiniteLogState
        {
            self.state@
        }

        pub closed spec fn pm_impervious_to_corruption(self) -> bool
        {
            self.wrpm.impervious_to_corruption()
        }

        pub closed spec fn valid(self) -> bool
        {
            &&& self.untrusted_log_impl.consistent_with_pm2(self.wrpm@)
            &&& can_only_crash_as_state(self.wrpm@, self.state@)
        }

        /// This static function takes a `PersistentMemory` and writes
        /// to it such that its state represents an empty log starting
        /// at head position 0. This function is meant to be called
        /// exactly once per log, to create and initialize it.
        pub exec fn setup(pm: &mut PersistentMemory) -> (result: Result<u64, InfiniteLogErr>)
            ensures
                match result {
                    Ok(capacity) => can_only_crash_as_state(pm@, AbstractInfiniteLogState::initialize(capacity as int)),
                    Err(InfiniteLogErr::InsufficientSpaceForSetup{ required_space }) =>
                        pm@.state.len() < required_space,
                    _ => false
                }
        {
            UntrustedLogImpl::untrusted_setup(pm)
        }

        /// This static function takes a `PersistentMemory` and wraps
        /// it into an `InfiniteLogImpl`. It's meant to be called after
        /// setting up the persistent memory or after crashing and
        /// restarting.
        pub exec fn start(pm: PersistentMemory) -> (result: Result<InfiniteLogImpl, InfiniteLogErr>)
            requires
                exists |state| can_only_crash_as_state(pm@, state)
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& forall |state| can_only_crash_as_state(pm@, state) ==> trusted_log_impl@ == state
                        &&& trusted_log_impl.pm_impervious_to_corruption() == pm.impervious_to_corruption()
                    },
                    Err(InfiniteLogErr::CRCMismatch) => !pm.impervious_to_corruption(),
                    _ => false
                }
        {
            // The untrusted `start` routine may write to persistent memory, as long
            // as it keeps its abstraction as a log unchanged.
            let mut wrpm = WriteRestrictedPersistentMemory::new(pm);
            let ghost state = choose |state| can_only_crash_as_state(pm@, state);
            let tracked perm = TrustedPermission::new(state, |s1, s2| false);
            match UntrustedLogImpl::untrusted_start(&mut wrpm, Tracked(&perm), Ghost(state)) {
                Ok(untrusted_log_impl) => Ok(InfiniteLogImpl { untrusted_log_impl, wrpm, state: Ghost(state) }),
                Err(e) => Err(e)
            }
        }

        /// This function appends to the log and returns the offset at
        /// which the append happened.
        pub exec fn append(&mut self, bytes_to_append: &Vec<u8>) -> (result: Result<u64, InfiniteLogErr>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                self.pm_impervious_to_corruption() == old(self).pm_impervious_to_corruption(),
                match result {
                    Ok(offset) => {
                        let old_log = old(self)@;
                        &&& offset as nat == old_log.log.len() + old_log.head
                        &&& self@ == old_log.append(bytes_to_append@)
                    },
                    Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append.len()
                        &&& {
                               ||| available_space == self@.capacity - self@.log.len()
                               ||| available_space == u64::MAX - self@.head - self@.log.len()
                           }
                    },
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with `bytes_to_append`
            // appended.

            let tracked perm = TrustedPermission::new(self.state@,
                |s1: AbstractInfiniteLogState, s2| s2 == s1.append(bytes_to_append@));
            let result = self.untrusted_log_impl.untrusted_append(&mut self.wrpm, bytes_to_append, Tracked(&perm),
                                                                  self.state);
            self.state = if result.is_ok() { Ghost(self.state@.append(bytes_to_append@)) } else { self.state };
            result
        }

        /// This function advances the head index of the log.
        pub exec fn advance_head(&mut self, new_head: u64) -> (result: Result<(), InfiniteLogErr>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                self.pm_impervious_to_corruption() == old(self).pm_impervious_to_corruption(),
                match result {
                    Ok(offset) => {
                        let old_log = old(self)@;
                        &&& old_log.head <= new_head <= old_log.head + old_log.log.len()
                        &&& self@ == old_log.advance_head(new_head as int)
                    },
                    Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.head
                        &&& new_head < head
                    },
                    Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.head + self@.log.len()
                        &&& new_head > tail
                    },
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with the head advanced to
            // `new_head`.

            let tracked perm = TrustedPermission::new(self.state@,
                |s1: AbstractInfiniteLogState, s2| s2 == s1.advance_head(new_head as int));
            let result = self.untrusted_log_impl.untrusted_advance_head(&mut self.wrpm, new_head, Tracked(&perm),
                                                                        self.state);
            self.state = if result.is_ok() { Ghost(self.state@.advance_head(new_head as int)) } else { self.state };
            result
        }

        /// This function reads `len` bytes from byte position `pos`
        /// in the log. It returns a vector of those bytes.
        pub exec fn read(&self, pos: u64, len: u64) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), InfiniteLogErr>)
            requires
                self.valid(),
                pos + len <= u64::MAX
            ensures
                ({
                    let head = self@.head;
                    let log = self@.log;
                    match result {
                        Ok((bytes, addrs)) => {
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& maybe_corrupted(bytes@, log.subrange(pos - head, pos + len - head), addrs@)
                            &&& self.pm_impervious_to_corruption() ==>
                                   bytes@ == log.subrange(pos - head, pos + len - head)
                        },
                        Err(InfiniteLogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(InfiniteLogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > head + log.len()
                            &&& tail == head + log.len()
                        },
                        _ => false
                    }
                })
        {
            // We don't need to provide permission to write to the
            // persistent memory because the untrusted code is only
            // getting a non-mutable reference to it and thus can't
            // write it. Note that the `UntrustedLogImpl` itself *is*
            // mutable, so it can freely update its in-memory state
            // (e.g., its cache) if it chooses.
            self.untrusted_log_impl.untrusted_read(self.wrpm.get_pm_ref(), pos, len, self.state)
        }

        /// This function returns a tuple consisting of the head and
        /// tail positions of the log.
        pub exec fn get_head_and_tail(&self) -> (result: Result<(u64, u64, u64), InfiniteLogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == self@.head
                        &&& result_tail == self@.head + self@.log.len()
                        &&& result_capacity == self@.capacity
                    },
                    Err(_) => false
                }
        {
            // We don't need to provide permission to write to the
            // persistent memory because the untrusted code is only
            // getting a non-mutable reference to it and thus can't
            // write it. Note that the `UntrustedLogImpl` itself *is*
            // mutable, so it can freely update its in-memory state
            // (e.g., its local copy of head and tail) if it chooses.
            self.untrusted_log_impl.untrusted_get_head_and_tail(self.wrpm.get_pm_ref(), self.state)
        }
    }

}
