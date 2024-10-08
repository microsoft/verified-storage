//! This file contains the trusted implementation of a `LogImpl`.
//! Although the verifier is run on this file, it needs to be
//! carefully read and audited to be confident of the correctness of
//! this log implementation.
//!
//! Fortunately, it delegates most of its work to an untrusted struct
//! `UntrustedLogImpl`, which doesn't need to be read or audited. It
//! forces the `UntrustedLogImpl` to satisfy certain postconditions,
//! and also places restrictions on what `UntrustedLogImpl` can do to
//! persistent memory. These restrictions ensure that even if the
//! system or process crashes in the middle of an operation, the
//! system will still recover to a consistent state.
//!
//! It requires `UntrustedLogImpl` to implement routines that do the
//! various log operations like read and commit.
//!
//! It also requires `UntrustedLogImpl` to provide a function
//! `UntrustedLogImpl::recover`, which specifies what its `start`
//! routine will do to recover after a crash. It requires its `start`
//! routine to satisfy that specification. It also uses it to limit
//! how `UntrustedLogImpl` writes to memory: It can only perform
//! updates that, if incompletely performed before a crash, still
//! leave the system in a valid state. The `recover` function takes a
//! second parameter, the `log_id` which is passed to the start
//! routine.
//!
//! It also requires `UntrustedLogImpl` to provide a function `view`
//! that converts the current state into an abstract log. It requires
//! that performing a certain operation on the `UntrustedLogImpl`
//! causes a corresponding update to its abstract view. For instance,
//! calling the `u.commit()` method should cause the resulting
//! `u.view()` to become `old(u).view().commit()`.
//!
//! It also permits `UntrustedLogImpl` to provide a function `inv`
//! that encodes any invariants `UntrustedLogImpl` wants maintained
//! across invocations of its functions. This implementation will then
//! guarantee that `inv` holds on any call to an `UntrustedLogImpl`
//! method, and demand that the method preserve that invariant.

use std::fmt::Write;
use std::sync::Arc;

use crate::log::logimpl_v::UntrustedLogImpl;
use crate::log::logspec_t::AbstractLogState;
use crate::log::wrpm_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmem_prophspec_v::*;
use crate::pmem::wrpm_v::*;
use crate::pmem::pmemspec2_t::*;
use crate::pmem::pmemadapt_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::modes::*;

use deps_hack::rand::Rng;

verus! {

    // This is the specification that `LogImpl` provides for data
    // bytes it reads. It says that those bytes are correct unless
    // there was corruption on the persistent memory between the last
    // write and this read.
    pub open spec fn read_correct_modulo_corruption(bytes: Seq<u8>, true_bytes: Seq<u8>,
                                                    impervious_to_corruption: bool) -> bool
    {
        if impervious_to_corruption {
            // If the region is impervious to corruption, the bytes read
            // must match the true bytes, i.e., the bytes last written.

            bytes == true_bytes
        }
        else {
            // Otherwise, there must exist a sequence of distinct
            // addresses `addrs` such that the nth byte of `bytes` is
            // a possibly corrupted version of the nth byte of
            // `true_bytes` read from the nth address in `addrs`.  We
            // don't require the sequence of addresses to be
            // contiguous because the data might not be contiguous on
            // disk (e.g., if it wrapped around the log area).

            exists |addrs: Seq<int>| {
                &&& all_elements_unique(addrs)
                &&& #[trigger] maybe_corrupted(bytes, true_bytes, addrs)
            }
        }
    }

    // This specification function indicates whether the given view of
    // memory will crash in a way that, after recovery, leads to a
    // certain abstract state.
    pub open spec fn crashes_as_abstract_state(
        pm_region_view: PersistentMemoryRegionView,
        log_id: u128,
        state: AbstractLogState,
    ) -> bool
    {
        UntrustedLogImpl::recover(pm_region_view.durable_state, log_id) == Some(state)
    }

    pub struct AbstractLogCrashState {
        pub state1: AbstractLogState,
        pub state2: AbstractLogState,
    }

    pub open spec fn recover_into(s: Seq<u8>, log_id: u128, crash: AbstractLogCrashState) -> bool {
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state1) ||
        UntrustedLogImpl::recover(s, log_id) == Some(crash.state2)
    }

    // This enumeration represents the various errors that can be
    // returned from log operations. They're self-explanatory.
    // TODO: make `PmemErr` and `LogErr` handling cleaner
    #[derive(Debug)]
    pub enum LogErr {
        InsufficientSpaceForSetup { required_space: u64 },
        StartFailedDueToLogIDMismatch { log_id_expected: u128, log_id_read: u128 },
        StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
        StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
        StartFailedDueToInvalidMemoryContents,
        CRCMismatch,
        InsufficientSpaceForAppend { available_space: u64 },
        CantReadBeforeHead { head: u128 },
        CantReadPastTail { tail: u128 },
        CantAdvanceHeadPositionBeforeHead { head: u128 },
        CantAdvanceHeadPositionBeyondTail { tail: u128 },
        PmemErr { err: PmemError } // janky workaround so that callers can handle PmemErrors as LogErrors
    }

    // This executable method can be called to compute a random GUID.
    // It uses the external `rand` crate.
    #[verifier::external_body]
    pub exec fn generate_fresh_log_id() -> (out: u128)
    {
        deps_hack::rand::thread_rng().gen::<u128>()
    }

    // Invariant and write-restricted storage adapter.

    pub struct LogInvState {
        // State of the persistent memory from PersistentMemoryRegionV2.
        pub pm: FractionalResource<PersistentMemoryRegionView, 3>,

        // State of the abstract log on crash.
        pub crash: FractionalResource<AbstractLogCrashState, 2>,
    }

    pub struct LogInvParam {
        pub pm_frac_id: int,
        pub crash_frac_id: int,
        pub log_id: u128,
    }

    pub struct LogInvPred {}

    impl InvariantPredicate<LogInvParam, LogInvState> for LogInvPred {
        open spec fn inv(k: LogInvParam, v: LogInvState) -> bool {
            v.pm.valid(k.pm_frac_id, 1) &&
            v.crash.valid(k.crash_frac_id, 1) &&
            recover_into(v.pm.val().durable_state, k.log_id, v.crash.val())
        }
    }

    pub exec fn add_possible_crash_state(Tracked(inv): Tracked<&AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>,
                                         Tracked(abs): Tracked<&mut FractionalResource<AbstractLogCrashState, 2>>,
                                         Ghost(new_state): Ghost<AbstractLogState>)
        requires
            old(abs).valid(inv.constant().crash_frac_id, 1),
            old(abs).val().state1 == old(abs).val().state2,
        ensures
            abs.valid(inv.constant().crash_frac_id, 1),
            abs.val() == (AbstractLogCrashState{ state1: old(abs).val().state1, state2: new_state }),
    {
        open_atomic_invariant!(inv => inner => { proof {
            abs.combine_mut(inner.crash);
            abs.update_mut(AbstractLogCrashState{
                state1: abs.val().state1,
                state2: new_state,
            });
            inner.crash = abs.split_mut(1);

            assert forall |s| recover_into(s, inv.constant().log_id@,
                                           AbstractLogCrashState{
                                               state1: abs.val().state1,
                                               state2: abs.val().state1,
                                           })
                implies #[trigger] recover_into(s, inv.constant().log_id@, abs.val()) by {};
        }});
    }

    pub exec fn set_unique_crash_state(Tracked(inv): Tracked<&AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>,
                                       Tracked(abs): Tracked<&mut FractionalResource<AbstractLogCrashState, 2>>,
                                       Tracked(pm): Tracked<&FractionalResource<PersistentMemoryRegionView, 3>>,
                                       Ghost(new_state): Ghost<AbstractLogState>)
        requires
            old(abs).valid(inv.constant().crash_frac_id, 1),
            pm.valid(inv.constant().pm_frac_id, 1),
            crashes_as_abstract_state(pm.val(), inv.constant().log_id, new_state),
        ensures
            abs.valid(inv.constant().crash_frac_id, 1),
            abs.val() == (AbstractLogCrashState{ state1: new_state, state2: new_state }),
    {
        open_atomic_invariant!(inv => inner => { proof {
            abs.combine_mut(inner.crash);
            abs.update_mut(AbstractLogCrashState{
                state1: new_state,
                state2: new_state,
            });
            inner.crash = abs.split_mut(1);
            inner.pm.agree(pm);
        }});
    }

    /// A `LogImpl` wraps one `UntrustedLogImpl` and one persistent
    /// memory region to provide the executable interface that turns
    /// the persistent memory region into a log.
    ///
    /// The `untrusted_log_impl` field is the wrapped
    /// `UntrustedLogImpl`.
    ///
    /// The `log_id` field is the log ID. It's ghost.
    ///
    /// The `wrpm_region` field contains the write-restricted persistent
    /// memory. This memory will only allow updates allowed by a
    /// tracked `Permission`. So we can pass `wrpm_region` to an
    /// untrusted method, along with a restricting
    /// `Permission`, to limit what it's allowed to do.

    pub struct LogImpl<PMRegion: PersistentMemoryRegion> {
        untrusted_log_impl: UntrustedLogImpl,
        log_id: Ghost<u128>,
        wrpm_region: WriteRestrictedPersistentMemoryRegionV2<PMRegionV2<PMRegion>>,
        abs: Tracked<FractionalResource<AbstractLogCrashState, 2>>,
        inv: Tracked<Arc<AtomicInvariant<LogInvParam, LogInvState, LogInvPred>>>,
    }

    impl <PMRegion: PersistentMemoryRegion> LogImpl<PMRegion> {
        // The view of a `LogImpl` is whatever the
        // `UntrustedLogImpl` it wraps says it is.
        pub closed spec fn view(self) -> AbstractLogState
        {
            self.untrusted_log_impl@
        }

        // The constants of a `LogImpl` are whatever the
        // persistent memory it wraps says they are.
        pub closed spec fn constants(&self) -> PersistentMemoryConstants {
            self.wrpm_region.constants()
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
            &&& self.untrusted_log_impl.inv(&self.wrpm_region, self.log_id@)
            &&& self.abs@.valid(self.inv@.constant().crash_frac_id, 1)
            &&& self.abs@.val() == AbstractLogCrashState{ state1: self@.drop_pending_appends(), state2: self@.drop_pending_appends() }
            &&& self.log_id@ == self.inv@.constant().log_id
            &&& self.wrpm_region.inv()
            &&& self.wrpm_region.id() == self.inv@.constant()
        }

        // The `setup` method sets up persistent memory regions
        // `pm_region` to store an initial empty log. It returns a
        // vector listing the capacity of the log as well as a
        // fresh log ID to uniquely identify it. See `README.md`
        // for more documentation.
        pub exec fn setup(pm_region: &mut PMRegion) -> (result: Result<(u64, u128), LogErr>)
            requires
                old(pm_region).inv(),
                old(pm_region)@.valid(),
            ensures
                pm_region.inv(),
                pm_region@.valid(),
                match result {
                    Ok((log_capacity, log_id)) => {
                        let state = AbstractLogState::initialize(log_capacity as int);
                        &&& log_capacity <= pm_region@.len()
                        &&& pm_region@.len() == old(pm_region)@.len()
                        &&& crashes_as_abstract_state(pm_region@, log_id, state)
                        &&& pm_region@.read_state == pm_region@.durable_state
                        &&& state == state.drop_pending_appends()
                    },
                    Err(LogErr::InsufficientSpaceForSetup { required_space }) => {
                        &&& pm_region@ == old(pm_region)@
                        &&& pm_region@.len() < required_space
                    },
                    _ => false
                }
        {
            let log_id = generate_fresh_log_id();
            let capacities = UntrustedLogImpl::setup(pm_region, log_id)?;
            Ok((capacities, log_id))
        }

        // The `start` method creates an `UntrustedLogImpl` out of a
        // persistent memory region. It's assumed that the region was
        // initialized with `setup` and then only log operations were
        // allowed to mutate them. See `README.md` for more
        // documentation and an example of use.
        pub exec fn start(pm_region: PMRegion, log_id: u128) -> (result: Result<LogImpl<PMRegion>, LogErr>)
            requires
                pm_region.inv(),
                pm_region@.valid(),
                pm_region@.read_state == pm_region@.durable_state,
                UntrustedLogImpl::recover(pm_region@.durable_state, log_id).is_Some(),
            ensures
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& trusted_log_impl.constants() == pm_region.constants()
                        &&& crashes_as_abstract_state(pm_region@, log_id, trusted_log_impl@)
                    },
                    Err(LogErr::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                }
        {
            // We allow the untrusted `start` method to update memory
            // as part of its initialization. But, to avoid bugs
            // stemming from crashes in the middle of this routine, we
            // must restrict how it updates memory. We must only let
            // it write such that, if a crash happens in the middle,
            // it doesn't change the persistent state.

            let (mut pm_region2, Tracked(mut frac)) = PMRegionV2::new(pm_region);

            let ghost state = UntrustedLogImpl::recover(pm_region@.durable_state, log_id).get_Some_0();
            let tracked abs = FractionalResource::<AbstractLogCrashState, 2>::alloc(AbstractLogCrashState{
                state1: state,
                state2: state,
            });

            let ghost iparam = LogInvParam {
                pm_frac_id: pm_region2.id(),
                crash_frac_id: abs.id(),
                log_id: log_id,
            };
            let tracked istate = LogInvState {
                pm: frac.split_mut(1),
                crash: abs.split_mut(1),
            };
            let tracked inv = AtomicInvariant::<_, _, LogInvPred>::new(iparam, istate, 12345);
            let tracked inv = Arc::new(inv);

            let mut wrpm_region = WriteRestrictedPersistentMemoryRegionV2::new(pm_region2, Tracked(frac), Tracked(inv.clone()));
            let tracked perm = PermissionV2::new(&abs, iparam);
            let untrusted_log_impl =
                UntrustedLogImpl::start(&mut wrpm_region, log_id, Tracked(&perm), Ghost(state))?;

            set_unique_crash_state(Tracked(&inv),
                                   Tracked(&mut abs),
                                   Tracked(wrpm_region.frac.borrow()),
                                   Ghost(state.drop_pending_appends()));

            Ok(
                LogImpl {
                    untrusted_log_impl,
                    log_id: Ghost(log_id),
                    wrpm_region,
                    abs: Tracked(abs),
                    inv: Tracked(inv),
                },
            )
        }

        // The `tentatively_append` method tentatively appends
        // `bytes_to_append` to the end of the log. It's tentative in
        // that crashes will undo the appends, and reads aren't
        // allowed in the tentative part of the log. See `README.md` for
        // more documentation and examples of use.
        pub exec fn tentatively_append(&mut self, bytes_to_append: &[u8]) -> (result: Result<u128, LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(offset) => {
                        let state = old(self)@;
                        &&& offset == state.head + state.log.len() + state.pending.len()
                        &&& self@ == old(self)@.tentatively_append(bytes_to_append@)
                    },
                    Err(LogErr::InsufficientSpaceForAppend { available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                               ||| available_space == self@.capacity - self@.log.len() - self@.pending.len()
                               ||| available_space == u128::MAX - self@.head - self@.log.len() - self@.pending.len()
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
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            self.untrusted_log_impl.tentatively_append(&mut self.wrpm_region, bytes_to_append,
                                                       self.log_id, Tracked(&perm))
        }

        // The `commit` method atomically commits all tentative
        // appends that have been done to `self` since the last
        // commit. The commit is atomic in that even if there's a
        // crash in the middle, the recovered-to state either reflects
        // all those tentative appends or none of them. See `README.md`
        // for more documentation and examples of use.
        pub exec fn commit(&mut self) -> (result: Result<(), LogErr>)
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
            add_possible_crash_state(Tracked(self.inv.borrow()),
                                     Tracked(self.abs.borrow_mut()),
                                     Ghost(self@.commit().drop_pending_appends()));
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            let res = self.untrusted_log_impl.commit(&mut self.wrpm_region, self.log_id, Tracked(&perm));
            set_unique_crash_state(Tracked(self.inv.borrow()),
                                   Tracked(self.abs.borrow_mut()),
                                   Tracked(self.wrpm_region.frac.borrow()),
                                   Ghost(self@.drop_pending_appends()));
            res
        }

        // The `advance_head` method advances the head of the log to
        // virtual new head position `new_head`. It doesn't do this
        // tentatively; it completes it durably before returning.
        // However, `advance_head` doesn't commit tentative appends;
        // to do that, you need a separate call to `commit`. See
        // `README.md` for more documentation and examples of use.
        pub exec fn advance_head(&mut self, new_head: u128) -> (result: Result<(), LogErr>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                match result {
                    Ok(()) => {
                        let state = old(self)@;
                        &&& state.head <= new_head <= state.head + state.log.len()
                        &&& self@ == old(self)@.advance_head(new_head as int)
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeforeHead { head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@.head
                        &&& new_head < head
                    },
                    Err(LogErr::CantAdvanceHeadPositionBeyondTail { tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@.head + self@.log.len()
                        &&& new_head > tail
                    },
                    _ => false,
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with the head advanced.
            add_possible_crash_state(Tracked(self.inv.borrow()),
                                     Tracked(self.abs.borrow_mut()),
                                     Ghost(self@.advance_head(new_head as int).drop_pending_appends()));
            let tracked perm = PermissionV2::new(self.abs.borrow(), self.inv@.constant());
            let res = self.untrusted_log_impl.advance_head(&mut self.wrpm_region, new_head,
                                                           self.log_id, Tracked(&perm));
            set_unique_crash_state(Tracked(self.inv.borrow()),
                                   Tracked(self.abs.borrow_mut()),
                                   Tracked(self.wrpm_region.frac.borrow()),
                                   Ghost(self@.drop_pending_appends()));
            res
        }

        // The `read` method reads `len` bytes from the log starting
        // at virtual position `pos`. It isn't allowed to read earlier
        // than the head or past the committed tail. See `README.md` for
        // more documentation and examples of use.
        pub exec fn read(&self, pos: u128, len: u64) -> (result: Result<Vec<u8>, LogErr>)
            requires
                self.valid(),
                pos + len <= u128::MAX,
            ensures
                ({
                    let state = self@;
                    let head = state.head;
                    let log = state.log;
                    match result {
                        Ok(bytes) => {
                            let true_bytes = self@.read(pos as int, len as int);
                            &&& pos >= head
                            &&& pos + len <= head + log.len()
                            &&& read_correct_modulo_corruption(bytes@, true_bytes,
                                                             self.constants().impervious_to_corruption)
                        },
                        Err(LogErr::CantReadBeforeHead{ head: head_pos }) => {
                            &&& pos < head
                            &&& head_pos == head
                        },
                        Err(LogErr::CantReadPastTail{ tail }) => {
                            &&& pos + len > tail
                            &&& tail == head + log.len()
                        },
                        Err(e) => e == LogErr::PmemErr{ err: PmemError::AccessOutOfRange },
                    }
                })
        {
            let (bytes, addrs) = self.untrusted_log_impl.read(&self.wrpm_region, pos, len, self.log_id)?;
            Ok(bytes)
        }

        // The `get_head_tail_and_capacity` method returns three
        // pieces of metadata about the log: the virtual head
        // position, the virtual tail position, and the capacity. The
        // capacity is the maximum number of bytes there can be in the
        // log past the head, including bytes in tentative appends
        // that haven't been committed yet. See `README.md` for more
        // documentation and examples of use.
        pub exec fn get_head_tail_and_capacity(&self) -> (result: Result<(u128, u128, u64), LogErr>)
            requires
                self.valid()
            ensures
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == self@.head
                        &&& result_tail == self@.head + self@.log.len()
                        &&& result_capacity == self@.capacity
                    },
                    _ => false
                }
        {
            self.untrusted_log_impl.get_head_tail_and_capacity(&self.wrpm_region, self.log_id)
        }
    }

}
