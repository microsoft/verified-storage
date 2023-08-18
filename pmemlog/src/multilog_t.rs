use crate::infinitelog_t::*;
use crate::logimpl_v;
use crate::multilog_v::*;
use crate::pmemspec_t::*;
// use crate::main_t::*; // TODO: rename this file if they are going to be kept separate
use crate::sccf::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::bytes::*;

verus! {

    pub open spec fn recovery_view() -> (result: FnSpec(Seq<Seq<u8>>) -> Option<MultiLogAbstractInfiniteLogState>)
    {
        |multilog| UntrustedMultiLogImpl::convert_multilog_to_log_state(multilog)
    }

    pub open spec fn can_only_crash_as_state(multilog: MultiLogPersistentMemoryView, state: MultiLogAbstractInfiniteLogState) -> bool
    {
        forall |s| #[trigger] multilog.can_crash_as(s) ==> recovery_view()(s) == Some(state)
    }

    pub proof fn lemma_can_crash_as_same_state(
        view1: MultiLogPersistentMemoryView, 
        view2: MultiLogPersistentMemoryView, 
        state: MultiLogAbstractInfiniteLogState
    )
        requires 
            view1 == view2,
            can_only_crash_as_state(view1, state)
        ensures 
            can_only_crash_as_state(view2, state)
    {}

    pub struct TrustedMultiLogPermission {
        ghost is_state_allowable: FnSpec(Seq<Seq<u8>>) -> bool
    }

    impl CheckPermission<Seq<Seq<u8>>> for TrustedMultiLogPermission {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedMultiLogPermission {
        proof fn new(cur: MultiLogAbstractInfiniteLogState,
                    next: FnSpec(MultiLogAbstractInfiniteLogState, MultiLogAbstractInfiniteLogState) -> bool)
                    -> (tracked perm: Self)
            ensures 
                forall |s| #[trigger] perm.check_permission(s) <==>
                    crate::sccf::is_state_allowable(cur, s, recovery_view(), next)
        {
            Self { is_state_allowable: |s| crate::sccf::is_state_allowable(cur, s, recovery_view(), next) }
        }
    }

    /// An `InfiniteMultiLogImpl` wraps one `UntrustedLogImpl` and 
    /// one or more persistent memory regions to provide the 
    /// executable interface that turns the persistent memory
    /// regions into a set of infinite logs in which any subset
    /// of logs can be updated atomically
    pub struct InfiniteMultiLogImpl {
        // TODO: make these private
        pub untrusted_log_impl: UntrustedMultiLogImpl,
        pub wrpms: MultiLogWriteRestrictedPersistentMemory<TrustedMultiLogPermission>,
        pub state: Ghost<MultiLogAbstractInfiniteLogState>
    }

    impl InfiniteMultiLogImpl {
        pub closed spec fn view(self) -> MultiLogAbstractInfiniteLogState
        {
            self.state@
        }

        pub closed spec fn pm_impervious_to_corruption(self) -> bool {
            self.wrpms.impervious_to_corruption()
        }

        pub closed spec fn valid(self) -> bool {
            &&& self.untrusted_log_impl.consistent_with_multilog(self.wrpms@)
            &&& can_only_crash_as_state(self.wrpms@, self.state@)
        }

        /// Uses the 0th device to store header information. 
        pub exec fn setup(regions: &mut MultiLogPersistentMemory) -> (result: Result<Vec<u64>, InfiniteMultiLogErr>)
            ensures 
                match result {
                    Ok(capacities) => {
                        &&& capacities@.len() == regions@.len()
                        &&& UntrustedMultiLogImpl::convert_multilog_to_log_state(regions@.committed()) == Some(MultiLogAbstractInfiniteLogState::initialize(capacities@))
                        &&& capacities[0] == UntrustedMultiLogImpl::minimum_header_region_size(regions@.len() - 1)
                    },
                    Err(InfiniteMultiLogErr::InsufficientSpaceForSetup { pm_index, required_space }) => 
                        regions@[pm_index as int].len() < required_space,
                    _ => false
                }
        {
            UntrustedMultiLogImpl::untrusted_setup(regions)
        }

        pub exec fn start(regions: MultiLogPersistentMemory) -> (result: Result<InfiniteMultiLogImpl, InfiniteMultiLogErr>)
            requires 
                exists |s| can_only_crash_as_state(regions@, s),
                ({
                    let (_, headers) = multilog_to_views(regions@.committed()[0]);
                    let log_num = spec_u64_from_le_bytes(headers.log_num_bytes);
                    log_num == regions@.committed().len() - 1
                })
            ensures 
                match result {
                    Ok(trusted_log_impl) => {
                        &&& trusted_log_impl.valid()
                        &&& forall |s| can_only_crash_as_state(regions@, s) ==> trusted_log_impl@ == s
                        &&& trusted_log_impl.pm_impervious_to_corruption() == regions.impervious_to_corruption()
                    }
                    Err(InfiniteMultiLogErr::CRCMismatch) => !regions.impervious_to_corruption(),
                    Err(InfiniteMultiLogErr::InsufficientSpaceForSetup { pm_index, required_space }) => {
                        // TODO: handle once you actually return this error
                        true
                        // &&& 0 <= pm_index < regions@.len() ==> regions@[pm_index as int].len() < required_space
                        // &&& !(0 <= pm_index < regions@.len()) ==> false
                    }
                    _ => false
                }
        {
            let mut wrpms = MultiLogWriteRestrictedPersistentMemory::new(regions);
            let ghost state = choose |s| can_only_crash_as_state(regions@, s);
            let tracked perm = TrustedMultiLogPermission::new(state, |s1, s2| false);
            match UntrustedMultiLogImpl::untrusted_start(&mut wrpms, Tracked(&perm), Ghost(state)) {
                Ok(untrusted_log_impl) => {
                    Ok(InfiniteMultiLogImpl { untrusted_log_impl, wrpms, state: Ghost(state) })
                }
                Err(e) => Err(e)
            }
        }

        // TODO: update for new interface
        pub exec fn append(&mut self, index: usize, bytes_to_append: &Vec<u8>) -> (result: Result<u64, InfiniteMultiLogErr>)
            requires 
                old(self).valid()
            ensures 
                self.valid(),
                self.pm_impervious_to_corruption() == old(self).pm_impervious_to_corruption(),
                match result {
                    Ok(offset) => {
                        &&& offset as nat == old(self)@[index as int].log.len() + old(self)@[index as int].head 
                        &&& self@ == old(self)@.append(index as int, bytes_to_append@)
                    }
                    Err(InfiniteMultiLogErr::InsufficientSpaceForAppend { pm_index, available_space }) => {
                        &&& self@ == old(self)@
                        &&& available_space < bytes_to_append@.len()
                        &&& {
                                ||| available_space == self@[pm_index as int].capacity - self@[pm_index as int].log.len() 
                                ||| available_space == u64::MAX - self@[pm_index as int].head - self@[pm_index as int].log.len()
                            }
                    }
                    _ => false
                }
        {
            // For crash safety, we must restrict the untrusted code's
            // writes to persistent memory. We must only let it write
            // such that, if a crash happens in the middle of a write,
            // the view of the persistent state is either the current
            // state or the current state with `bytes_to_append`
            // appended.
            let tracked perm = TrustedMultiLogPermission::new(self.state@, 
                |s1: MultiLogAbstractInfiniteLogState, s2| s2 == s1.append(index as int, bytes_to_append@));
            assume(false);
            self.untrusted_log_impl.untrusted_append(&mut self.wrpms, index, bytes_to_append, Tracked(&perm))
        }

        pub exec fn advance_head(&mut self, index: usize, new_head: u64) -> (result: Result<(), InfiniteMultiLogErr>)
            requires 
                old(self).valid(),
            ensures 
                self.valid(),
                self.pm_impervious_to_corruption() == old(self).pm_impervious_to_corruption(),
                match result {
                    Ok(()) => {
                        let i = index as int;
                        &&& old(self)@[i].head <= new_head <= old(self)@[i].head + old(self)@[i].log.len()
                        &&& self@ == old(self)@.advance_head(i, new_head as int)
                    },
                    Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeforeHead { pm_index, head }) => {
                        &&& self@ == old(self)@
                        &&& head == self@[pm_index as int].head 
                        &&& new_head < head
                    }
                    Err(InfiniteMultiLogErr::CantAdvanceHeadPositionBeyondTail { pm_index, tail }) => {
                        &&& self@ == old(self)@
                        &&& tail == self@[pm_index as int].head + self@[pm_index as int].log.len()
                        &&& new_head > tail
                    }
                    Err(InfiniteMultiLogErr::InvalidIndex{ pm_index }) => {
                        pm_index > self@.len()
                    }
                    _ => false
                }
        {
            let tracked perm = TrustedMultiLogPermission::new(self.state@, 
                |s1: MultiLogAbstractInfiniteLogState, s2| s2 == s1.advance_head(index as int, new_head as int));
            let result = self.untrusted_log_impl.untrusted_advance_head(&mut self.wrpms, index, new_head, Tracked(&perm), self.state);
            assume(false);
            result
        }

        pub exec fn read(&self, index: usize, pos: u64, len: u64) -> (result: Result<(Vec<u8>, Ghost<Seq<int>>), InfiniteMultiLogErr>)
            requires 
                self.valid(),
                pos + len <= u64::MAX,
            ensures 
                match (self@[index as int]) {
                    AbstractInfiniteLogState { head, log, .. } => {
                        match result {
                            Ok((bytes, addrs)) => {
                                &&& pos >= head
                                &&& pos + len <= head + log.len()
                                &&& maybe_corrupted(bytes@, log.subrange(pos - head, pos + len - head), addrs@)
                                &&& self.pm_impervious_to_corruption() ==>
                                       bytes@ == log.subrange(pos - head, pos + len - head)
                            },
                            Err(InfiniteMultiLogErr::CantReadBeforeHead{ head: head_pos }) => {
                                &&& pos < head
                                &&& head_pos == head
                            },
                            Err(InfiniteMultiLogErr::CantReadPastTail{ tail }) => {
                                &&& pos + len > head + log.len()
                                &&& tail == head + log.len()
                            },
                            Err(InfiniteMultiLogErr::InvalidIndex { pm_index }) => {
                                &&& pm_index == index 
                                &&& pm_index >= self.untrusted_log_impl.log_metadata@.len()
                            }
                            _ => false
                        }
                    }
                }
        {
            // proof { self.wrpms.lemma_views_eq(); }
            // assert(self.wrpms.spec_get_pms()@.committed() =~= self.wrpms@.committed());
            let result = self.untrusted_log_impl.untrusted_read(self.wrpms.get_pms_ref(), index, pos, len, self.state);
            result
        }

        pub exec fn get_head_and_tail(&self, index: usize) -> (result: Result<(u64, u64, u64), InfiniteMultiLogErr>)
            requires 
                self.valid(),
            ensures 
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        let inf_log = self@[index as int];
                        &&& result_head == inf_log.head
                        &&& result_tail == inf_log.head + inf_log.log.len()
                        &&& result_capacity == inf_log.capacity
                    }
                    _ => false
                }
        {
            assume(false);
            Err(InfiniteMultiLogErr::None)
        }

    }
    

} // verus!