use std::fmt::Write;

use crate::infinitelog_t::*;
use crate::logimpl_v::*;
use crate::pmemspec_t::*;
use crate::sccf::CheckPermission;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;
use vstd::slice::*;

verus! {

    pub open spec fn recovery_view() -> (result: FnSpec(Seq<u8>) -> Option<AbstractInfiniteLogState>)
    {
        |c| UntrustedLogImpl::recover(c)
    }

    pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                    impervious_to_corruption: bool) -> bool
    {
        if impervious_to_corruption {
            bytes == true_bytes
        }
        else {
            exists |addrs: Seq<int>| {
                &&& addrs.no_duplicates()
                &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
            }
        }
    }

    /// A `TrustedPermission` indicates what states of persistent
    /// memory are permitted. The struct isn't public, so it can't be
    /// created outside of this file. As a further defense against one
    /// being created outside this file, its fields aren't public, and
    /// the constructor `TrustedPermission::new` isn't public.

    struct TrustedPermission {
        ghost is_state_allowable: FnSpec(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedPermission {
        closed spec fn permits(&self, state: Seq<u8>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedPermission {
        proof fn new(cur: Seq<u8>, next: FnSpec(AbstractInfiniteLogState, AbstractInfiniteLogState) -> bool)
                     -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.permits(s) <==>
                    crate::sccf::is_state_allowable(cur, s, recovery_view(), next)
        {
            Self { is_state_allowable: |s| crate::sccf::is_state_allowable(cur, s, recovery_view(), next) }
        }
    }

    /// A `InfiniteLogImpl` wraps an `UntrustedLogImpl` to provide the
    /// executable interface that turns a persistent memory region
    /// into an effectively infinite log. It provides a simple
    /// interface to higher-level code.
    pub struct InfiniteLogImpl<PM: PersistentMemory> {
        untrusted_log_impl: UntrustedLogImpl,
        wrpm: WriteRestrictedPersistentMemory<TrustedPermission, PM>,
    }

    #[derive(Debug)]
    pub enum InfiniteLogErr {
        InsufficientSpaceForSetup { required_space: u64 },
        CantReadBeforeHead { head: u64 },
        CantReadPastTail { tail: u64 },
        InsufficientSpaceForAppend { available_space: u64 },
        CRCMismatch,
        CantAdvanceHeadPositionBeforeHead { head: u64 },
        CantAdvanceHeadPositionBeyondTail { tail: u64 },
    }

    impl <PM: PersistentMemory> InfiniteLogImpl<PM> {
        pub closed spec fn view(self) -> Option<AbstractInfiniteLogState>
        {
            recovery_view()(self.wrpm@)
        }

        pub closed spec fn constants(self) -> PersistentMemoryConstants
        {
            self.wrpm.constants()
        }

        pub closed spec fn valid(self) -> bool {
            &&& self.untrusted_log_impl.inv(&self.wrpm)
            &&& recovery_view()(self.wrpm@).is_Some()
        }

        /// This static function takes a `PersistentMemory` and writes
        /// to it such that its state represents an empty log starting
        /// at head position 0. This function is meant to be called
        /// exactly once per log, to create and initialize it.
        pub exec fn setup(pm: &mut PM, device_size: u64) -> (result: Result<u64, InfiniteLogErr>)
            requires
                old(pm).inv(),
                old(pm)@.len() == device_size
            ensures
                pm.inv(),
                pm.constants() == old(pm).constants(),
                pm@.len() == device_size,
                match result {
                    Ok(log_capacity) =>
                        recovery_view()(pm@) == Some(AbstractInfiniteLogState::initialize(log_capacity as int)),
                    Err(InfiniteLogErr::InsufficientSpaceForSetup{ required_space }) => device_size < required_space,
                    _ => false
                }
        {
            UntrustedLogImpl::untrusted_setup(pm, device_size)
        }

        /// This static function takes a `PersistentMemory` and wraps
        /// it into an `InfiniteLogImpl`. It's meant to be called after
        /// setting up the persistent memory or after crashing and
        /// restarting.
        pub exec fn start(pm: PM, device_size: u64) -> (result: Result<InfiniteLogImpl<PM>, InfiniteLogErr>)
            requires
                pm.inv(),
                pm@.len() == device_size,
                recovery_view()(pm@).is_Some()
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl@ == recovery_view()(pm@)
                        &&& trusted_log_impl.constants() == pm.constants()
                    },
                    Err(InfiniteLogErr::CRCMismatch) => !pm.constants().impervious_to_corruption,
                    _ => false
                }
        {
            // The untrusted `start` routine may write to persistent memory, as long
            // as it keeps its abstraction as a log unchanged.
            let mut wrpm = WriteRestrictedPersistentMemory::new(pm);
            let tracked perm = TrustedPermission::new(pm@, |s1, s2| false);
            match UntrustedLogImpl::untrusted_start(&mut wrpm, device_size, Tracked(&perm)) {
                Ok(untrusted_log_impl) => Ok(InfiniteLogImpl { untrusted_log_impl, wrpm }),
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
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) =>
                        match (old(self)@, self@) {
                            (Some(old_log), Some(new_log)) => {
                                &&& offset as nat == old_log.log.len() + old_log.head
                                &&& new_log == old_log.append(bytes_to_append@)
                            },
                            _ => false
                        },
                    Err(InfiniteLogErr::InsufficientSpaceForAppend{ available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append.len()
                        &&& {
                               let log = old(self)@.unwrap();
                               ||| available_space == log.capacity - log.log.len()
                               ||| available_space == u64::MAX - log.head - log.log.len()
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

            let tracked perm = TrustedPermission::new(self.wrpm@,
                |s1: AbstractInfiniteLogState, s2| s2 == s1.append(bytes_to_append@));
            self.untrusted_log_impl.untrusted_append(&mut self.wrpm, bytes_to_append, Tracked(&perm))
        }

        /// This function advances the head index of the log.
        pub exec fn advance_head(&mut self, new_head: u64) -> (result: Result<(), InfiniteLogErr>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) => {
                        match (old(self)@, self@) {
                            (Some(old_log), Some(new_log)) => {
                                &&& old_log.head <= new_head <= old_log.head + old_log.log.len()
                                &&& new_log == old_log.advance_head(new_head as int)
                            },
                            _ => false
                        }
                    }
                    Err(InfiniteLogErr::CantAdvanceHeadPositionBeforeHead{ head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.unwrap().head
                        &&& new_head < head
                    },
                    Err(InfiniteLogErr::CantAdvanceHeadPositionBeyondTail{ tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.unwrap().head + self@.unwrap().log.len()
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

            let tracked perm = TrustedPermission::new(self.wrpm@,
                |s1: AbstractInfiniteLogState, s2| s2 == s1.advance_head(new_head as int));
            self.untrusted_log_impl.untrusted_advance_head(&mut self.wrpm, new_head, Tracked(&perm))
        }

        /// This function reads `len` bytes from byte position `pos`
        /// in the log. It returns a vector of those bytes.
        pub exec fn read(&self, pos: u64, len: u64) -> (result: Result<Vec<u8>, InfiniteLogErr>)
            requires
                self.valid(),
                pos + len <= u64::MAX
            ensures
                ({
                    let state = self@.unwrap();
                    let head = state.head;
                    let log = state.log;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = log.subrange(pos - head, pos + len - head);
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                             self.constants().impervious_to_corruption)
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
            self.untrusted_log_impl.untrusted_read(&self.wrpm, pos, len)
        }

        /// This function returns a tuple consisting of the head and
        /// tail positions of the log.
        pub exec fn get_head_and_tail(&self) -> (result: Result<(u64, u64, u64), InfiniteLogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        let inf_log = self@.unwrap();
                        &&& result_head == inf_log.head
                        &&& result_tail == inf_log.head + inf_log.log.len()
                        &&& result_capacity == inf_log.capacity
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
            self.untrusted_log_impl.untrusted_get_head_and_tail(&self.wrpm)
        }
    }
}
