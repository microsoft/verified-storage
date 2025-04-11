#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::impl_v::UntrustedMultilogImpl;
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
    pub log_area_start: u64,
    pub log_area_len: u64,
    pub durable_head: u128,
    pub durable_head_addr: u64,
    pub durable_log_length: u64,
    pub tentative_head: u128,
    pub tentative_head_addr: u64,
    pub tentative_log_length: u64,
}

impl UntrustedMultilogImpl {
    pub open(super) spec fn valid<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& self.status@ is Quiescent
        &&& self.inv(powerpm_region)
    }

    pub(super) open(super) spec fn inv_single_log_constants_corresponds(
        &self,
        which_log: int,
        log_info: LogInfo,
        log_constants: SingleLogConstants,
    ) -> bool {
        &&& log_info.log_area_start == log_constants.log_area_start
        &&& log_info.log_area_len == log_constants.log_area_end - log_constants.log_area_start
    }

    pub(super) open(super) spec fn inv_recovery_mapping_corresponds<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& self.rm@.corresponds(powerpm_region@.durable_state)
        &&& self.rm@.c == self.mv@.c
        &&& self.rm@.state == self.mv@.durable
        &&& self.rm@.vm == self.vm@
        &&& self.rm@.sm == self.sm
        &&& self.rm@.mask_cdb == self.durable_mask_cdb
        &&& self.rm@.mask == self.durable_mask
    }

    pub(super) open(super) spec fn inv_logs_unmodified(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.logs_modified@.len() ==> 0 <= #[trigger] self.logs_modified@[i] < self.sm.num_logs
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            0 <= i < self.sm.num_logs && !self.logs_modified@.contains(i as u64) ==> {
                let info = self.log_infos@[i];
                &&& info.durable_head == info.tentative_head
                &&& info.durable_head_addr == info.tentative_head_addr
                &&& info.durable_log_length == info.tentative_log_length
            }
    }

    pub(super) open(super) spec fn inv_durable_metadata(
        info: LogInfo,
        state: AtomicLogState,
    ) -> bool {
        &&& info.durable_head == state.head
        &&& info.durable_log_length == state.log.len()
        &&& info.durable_head_addr == info.log_area_start + (state.head % (
        info.log_area_len as int))
    }

    pub(super) open(super) spec fn inv_tentative_metadata(
        info: LogInfo,
        state: AtomicLogState,
    ) -> bool {
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& info.tentative_head == state.head
        &&& info.tentative_log_length == state.log.len()
        &&& info.tentative_head_addr == info.log_area_start + (state.head % (
        info.log_area_len as int))
    }

    pub(super) open(super) spec fn inv_durable_log(
        info: LogInfo,
        state: AtomicLogState,
        s: Seq<u8>,
    ) -> bool {
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& forall|pos_relative_to_head: int|
            #![trigger state.log[pos_relative_to_head]]
            0 <= pos_relative_to_head < state.log.len() ==> {
                let addr = relative_log_pos_to_addr(
                    pos_relative_to_head,
                    info.durable_head_addr as int,
                    info.log_area_start as int,
                    log_area_end,
                );
                state.log[pos_relative_to_head] == s[addr]
            }
    }

    pub(super) open(super) spec fn inv_tentative_log(
        info: LogInfo,
        state: AtomicLogState,
        s: Seq<u8>,
    ) -> bool {
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& forall|pos_relative_to_head: int|
            #![trigger state.log[pos_relative_to_head]]
            0 <= pos_relative_to_head < state.log.len() ==> {
                let addr = relative_log_pos_to_addr(
                    pos_relative_to_head,
                    info.tentative_head_addr as int,
                    info.log_area_start as int,
                    log_area_end,
                );
                state.log[pos_relative_to_head] == s[addr]
            }
    }

    pub(super) open(super) spec fn inv_state_correspondence(
        &self,
        durable_state: Seq<u8>,
        read_state: Seq<u8>,
    ) -> bool {
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.durable.logs[i]]
            0 <= i < self.sm.num_logs ==> Self::inv_durable_metadata(
                self.log_infos@[i],
                self.mv@.durable.logs[i],
            )
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.tentative.logs[i]]
            0 <= i < self.sm.num_logs ==> Self::inv_tentative_metadata(
                self.log_infos@[i],
                self.mv@.tentative.logs[i],
            )
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.tentative.logs[i]]
            0 <= i < self.sm.num_logs ==> Self::inv_durable_log(
                self.log_infos@[i],
                self.mv@.durable.logs[i],
                durable_state,
            )
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.tentative.logs[i]]
            0 <= i < self.sm.num_logs ==> Self::inv_durable_log(
                self.log_infos@[i],
                self.mv@.durable.logs[i],
                read_state,
            )
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.tentative.logs[i]]
            0 <= i < self.sm.num_logs ==> Self::inv_tentative_log(
                self.log_infos@[i],
                self.mv@.tentative.logs[i],
                read_state,
            )
    }

    pub open(super) spec fn inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& powerpm_region.inv()
        &&& Self::recover(powerpm_region@.durable_state) == Some(self@.recover())
        &&& self.log_infos.len() == self.sm.num_logs
        &&& self.inv_logs_unmodified()
        &&& self.inv_recovery_mapping_corresponds(powerpm_region)
        &&& self.inv_state_correspondence(powerpm_region@.durable_state, powerpm_region@.read_state)
    }

    pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region),
        ensures
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
    {
    }

    pub proof fn lemma_inv_implies_powerpm_inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region),
        ensures
            powerpm_region.inv(),
    {
    }
}

} // verus!
