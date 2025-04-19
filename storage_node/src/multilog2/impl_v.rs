use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

//use super::inv_v::*;
use super::recover_v::*;
use super::spec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;

verus! {

#[verifier::ext_equal]
pub(super) enum MultilogStatus {
    Quiescent,
}

#[verifier::ext_equal]
pub(super) struct LogInfo {
    pub which_log: Ghost<u64>,
    pub log_area_start: u64,
    pub log_area_end: u64,
    pub log_area_len: u64,
    pub durable_head: u128,
    pub durable_head_addr: u64,
    pub durable_log_length: u64,
    pub durable_log: Ghost<Seq<u8>>,
    pub tentative_head: u128,
    pub tentative_head_addr: u64,
    pub tentative_log_length: u64,
    pub tentative_log: Ghost<Seq<u8>>,
}

#[verifier::ext_equal]
pub struct UntrustedMultilogImpl {
    pub(super) status: Ghost<MultilogStatus>,
    pub(super) vm: Ghost<MultilogVersionMetadata>,
    pub(super) sm: MultilogStaticMetadata,
    pub(super) log_infos: Vec<LogInfo>,
    pub(super) logs_modified: Vec<u64>,
    pub(super) durable_mask_cdb: bool,
    pub(super) durable_mask: u64,
    pub(super) rm: Ghost<MultilogRecoveryMapping>,
}

impl UntrustedMultilogImpl {
    // This static function specifies how multiple regions'
    // contents should be viewed upon recovery as an abstract
    // log state.
    pub open(super) spec fn recover(mem: Seq<u8>) -> Option<RecoveredMultilogState> {
        recover_state(mem)
    }

    // This function specifies how to view the in-memory state of
    // `self` as an abstract log state.
    pub open(super) spec fn view(&self) -> MultilogView {
        self.internal_view()@
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
        which_log: u64,
        bytes_to_append: &[u8],
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<u128, MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            old(self).valid(&*old(powerpm_region)),
            perm.valid(old(powerpm_region).id()),
            forall|s| #[trigger]
                perm.check_permission(s) <== Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.valid(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            match result {
                Ok(offset) => {
                    &&& which_log < old(self)@.tentative.num_logs()
                    &&& offset == old(self)@.tentative[which_log as int].tail()
                    &&& self@ == MultilogView {
                        tentative: old(self)@.tentative.append(which_log as int, bytes_to_append@),
                        ..self@
                    }
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
                _ => false,
            },
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn tentatively_advance_head<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        which_log: u64,
        new_head: u128,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            old(self).valid(&*old(powerpm_region)),
            perm.valid(old(powerpm_region).id()),
            forall|s| #[trigger]
                perm.check_permission(s) <== Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.valid(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            match result {
                Ok(()) => {
                    let state = old(self)@.tentative[which_log as int];
                    &&& which_log < old(self)@.tentative.num_logs()
                    &&& state.head <= new_head <= state.head + state.log.len()
                    &&& self@ == MultilogView {
                        tentative: old(self)@.tentative.advance_head(
                            which_log as int,
                            new_head as int,
                        ),
                        ..self@
                    }
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
                _ => false,
            },
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    // The `read` method reads part of one of the logs, returning a
    // vector containing the read bytes. It doesn't guarantee that
    // those bytes aren't corrupted by persistent memory corruption.
    // See `README.md` for more documentation and examples of its use.
    pub exec fn read<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        which_log: u64,
        pos: u128,
        len: u64,
    ) -> (result: Result<Vec<u8>, MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            self.valid(powerpm_region),
            pos + len <= u128::MAX,
        ensures
            ({
                let log = self@.tentative[which_log as int];
                match result {
                    Ok(bytes) => {
                        let true_bytes = self@.tentative.read(
                            which_log as int,
                            pos as int,
                            len as int,
                        );
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos >= log.head
                        &&& pos + len <= log.tail()
                        &&& read_correct_modulo_corruption(
                            bytes@,
                            true_bytes,
                            powerpm_region.constants(),
                        )
                    },
                    Err(MultilogErr::InvalidLogIndex) => which_log >= self@.tentative.num_logs(),
                    Err(MultilogErr::CantReadBeforeHead { head: head_pos }) => {
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos < log.head
                        &&& head_pos == log.head
                    },
                    Err(MultilogErr::CantReadPastTail { tail }) => {
                        &&& which_log < self@.tentative.num_logs()
                        &&& pos + len > log.tail()
                        &&& tail == log.tail()
                    },
                    _ => false,
                }
            }),
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn get_num_logs<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> (result: Result<u32, MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            self.valid(powerpm_region),
        ensures
            result is Ok,
            result.unwrap() == self@.tentative.num_logs(),
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }

    pub exec fn get_head_tail_and_capacity<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        which_log: u64,
    ) -> (result: Result<(u128, u128, u64), MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            self.valid(powerpm_region),
        ensures
            ({
                let log = self@.tentative[which_log as int];
                match result {
                    Ok((result_head, result_tail, result_capacity)) => {
                        &&& result_head == self@.tentative[which_log as int].head
                        &&& result_tail == self@.tentative[which_log as int].tail()
                        &&& result_capacity == self@.c.capacities[which_log as int]
                    },
                    Err(MultilogErr::InvalidLogIndex) => { which_log >= self@.tentative.num_logs()
                    },
                    _ => false,
                }
            }),
    {
        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }
}

} // verus!
