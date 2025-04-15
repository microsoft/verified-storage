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
    pub log_area_end: u64,
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

    pub(super) open(super) spec fn inv_recovery_mapping_consistent_with_other_fields(&self) -> bool
    {
        &&& self.rm@.c == self.mv@.c
        &&& self.rm@.state == self.mv@.durable
        &&& self.rm@.vm == self.vm@
        &&& self.rm@.sm == self.sm
        &&& self.rm@.mask_cdb == self.durable_mask_cdb
        &&& self.rm@.mask == self.durable_mask
        &&& forall|i: int| #![trigger self.log_infos@[i]] #![trigger self.rm@.all_log_constants[i]]
            0 <= i < self.sm.num_logs ==> {
                let info = self.log_infos@[i];
                let constants = self.rm@.all_log_constants[i];
                &&& info.log_area_start == constants.log_area_start
                &&& info.log_area_len == constants.log_area_end - constants.log_area_start
            }
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
        &&& info.log_area_end == info.log_area_start + info.log_area_len
        &&& info.durable_head == state.head
        &&& info.durable_log_length == state.log.len()
        &&& info.durable_head_addr == info.log_area_start + (state.head % (
        info.log_area_len as int))
        &&& info.durable_log_length <= info.log_area_len
        &&& info.log_area_start <= info.durable_head_addr < info.log_area_end
    }

    pub(super) open(super) spec fn inv_tentative_metadata(
        info: LogInfo,
        state: AtomicLogState,
    ) -> bool {
        &&& info.log_area_end == info.log_area_start + info.log_area_len
        &&& info.tentative_head == state.head
        &&& info.tentative_log_length == state.log.len()
        &&& info.tentative_head_addr == info.log_area_start + (state.head % (
        info.log_area_len as int))
        &&& info.tentative_log_length <= info.log_area_len
        &&& info.log_area_start <= info.tentative_head_addr < info.log_area_end
    }

    pub(super) open(super) spec fn inv_log_info_consistent_with_view(&self) -> bool
    {
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
    }

    pub(super) open(super) spec fn inv_state_corresponds_for_log(
        &self,
        durable_state: Seq<u8>,
        read_state: Seq<u8>,
        which_log: int
    ) -> bool {
        let info = self.log_infos@[which_log];
        &&& self.mv@.durable.logs[which_log].log == extract_log_given_metadata_values(
            durable_state,
            info.log_area_start as int,
            info.log_area_start + info.log_area_len,
            info.durable_log_length as int,
            info.durable_head as int
        )
        &&& self.mv@.durable.logs[which_log].log == extract_log_given_metadata_values(
            read_state,
            info.log_area_start as int,
            info.log_area_start + info.log_area_len,
            info.durable_log_length as int,
            info.durable_head as int
        )
        &&& self.mv@.tentative.logs[which_log].log == extract_log_given_metadata_values(
            read_state,
            info.log_area_start as int,
            info.log_area_start + info.log_area_len,
            info.tentative_log_length as int,
            info.tentative_head as int
        )
    }

    pub(super) open(super) spec fn inv_state_correspondence(
        &self,
        durable_state: Seq<u8>,
        read_state: Seq<u8>,
    ) -> bool {
        &&& forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.durable.logs[i]]
            0 <= i < self.sm.num_logs ==> self.inv_state_corresponds_for_log(durable_state, read_state, i)
    }

    pub open(super) spec fn inv_internal(&self) -> bool
    {
        &&& self.log_infos.len() == self.sm.num_logs
        &&& self.inv_logs_unmodified()
        &&& self.inv_log_info_consistent_with_view()
        &&& self.inv_recovery_mapping_consistent_with_other_fields()
    }

    pub open(super) spec fn inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& powerpm_region.inv()
        &&& self.inv_internal()
        &&& self.rm@.corresponds(powerpm_region@.durable_state)
        &&& self.inv_state_correspondence(powerpm_region@.durable_state, powerpm_region@.read_state)
    }

    pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region),
        ensures
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
    {
        self.rm@.lemma_corresponds_implies_equals_new(powerpm_region@.durable_state);
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
