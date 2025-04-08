#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use super::impl_v::UntrustedMultilogImpl;
use super::recover_v::*;

verus! {

pub(super) enum MultilogStatus
{
    Quiescent
}

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

pub(super) open spec fn is_valid_log_index(which_log: int, num_logs: int) -> bool
{
    0 <= which_log < num_logs
}

impl UntrustedMultilogImpl
{
    pub open(super) spec fn valid<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
    {
        &&& self.status@ is Quiescent
        &&& self.inv(powerpm_region)
    }

    pub(super) open(super) spec fn inv_single_log_constants_corresponds(
        &self,
        which_log: int,
        log_info: LogInfo,
        log_constants: SingleLogConstants,
    ) -> bool
    {
        &&& log_info.log_area_start == log_constants.log_area_start
        &&& log_info.log_area_len == log_constants.log_area_end - log_constants.log_area_start
    }

    pub(super) open(super) spec fn inv_log_constants_recoverable<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
    {
        match recover_all_log_constants(powerpm_region@.durable_state, self.sm) {
            Some(log_constants) =>
                forall|i: int| #[trigger] is_valid_log_index(i, self.sm.num_logs as int) ==>
                        self.inv_single_log_constants_corresponds(i, self.log_infos@[i],
                                                                  log_constants[i]),
            None => false,
        }
    }

    pub(super) open(super) spec fn inv_logs_unmodified(&self) -> bool
    {
        forall|i: int|
            #[trigger] is_valid_log_index(i, self.sm.num_logs as int) && !self.logs_modified@.contains(i as usize) ==> {
            let info = self.log_infos@[i];
            &&& info.durable_head == info.tentative_head
            &&& info.durable_head_addr == info.tentative_head_addr
            &&& info.durable_log_length == info.tentative_log_length
        }
    }

    pub(super) open(super) spec fn inv_durable_metadata(&self, which_log: int) -> bool
    {
        let info = self.log_infos@[which_log];
        let state = self.state@.durable.logs[which_log];
        &&& info.durable_head == state.head
        &&& info.durable_log_length == state.log.len()
        &&& info.durable_head_addr == info.log_area_start + (state.head % (info.log_area_len as int))
    }

    pub(super) open(super) spec fn inv_durable_log(&self, s: Seq<u8>, which_log: int) -> bool
    {
        let info = self.log_infos@[which_log];
        let state = self.state@.durable.logs[which_log];
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& forall|pos_relative_to_head: int| #![trigger state.log[pos_relative_to_head]]
                0 <= pos_relative_to_head < state.log.len() ==>
            {
                let addr = relative_log_pos_to_addr(pos_relative_to_head, info.durable_head_addr as int, info.log_area_start as int, log_area_end);
                state.log[pos_relative_to_head] == s[addr]
            }
    }

    pub(super) open(super) spec fn inv_tentative_metadata(&self, which_log: int) -> bool
    {
        let info = self.log_infos@[which_log];
        let state = self.state@.tentative.logs[which_log];
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& info.tentative_head == state.head
        &&& info.tentative_log_length == state.log.len()
        &&& info.tentative_head_addr == info.log_area_start + (state.head % (info.log_area_len as int))
    }

    pub(super) open(super) spec fn inv_tentative_log(&self, s: Seq<u8>, which_log: int) -> bool
    {
        let info = self.log_infos@[which_log];
        let state = self.state@.tentative.logs[which_log];
        let log_area_end = info.log_area_start + info.log_area_len;
        &&& forall|pos_relative_to_head: int| #![trigger state.log[pos_relative_to_head]]
                0 <= pos_relative_to_head < state.log.len() ==>
            {
                let addr = relative_log_pos_to_addr(pos_relative_to_head, info.tentative_head_addr as int, info.log_area_start as int, log_area_end);
                state.log[pos_relative_to_head] == s[addr]
            }
    }

    pub(super) open(super) spec fn inv_state_correspondence(&self, durable_state: Seq<u8>, read_state: Seq<u8>) -> bool
    {
        forall|i: int| #[trigger] is_valid_log_index(i, self.sm.num_logs as int) ==> {
            &&& self.inv_durable_metadata(i)
            &&& self.inv_tentative_metadata(i)
            &&& self.inv_durable_log(durable_state, i)
            &&& self.inv_durable_log(read_state, i)
            &&& self.inv_tentative_log(read_state, i)
        }
    }

    pub open(super) spec fn inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
    {
        &&& powerpm_region.inv()
        &&& Self::recover(powerpm_region@.durable_state) == Some(self@.recover())
        &&& recover_version_metadata(powerpm_region@.durable_state) == Some(self.vm@)
        &&& recover_static_metadata(powerpm_region@.durable_state, self.vm@) == Some(self.sm)
        &&& recover_mask(powerpm_region@.durable_state, self.sm) == Some(self.durable_mask)
        &&& self.inv_log_constants_recoverable(powerpm_region)
        &&& self.log_infos.len() == self.sm.num_logs
        &&& self.inv_logs_unmodified()
        &&& self.inv_state_correspondence(powerpm_region@.durable_state, powerpm_region@.read_state)
    }

    pub proof fn lemma_inv_implies_can_only_crash_as<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region),
        ensures
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
    {}

    pub proof fn lemma_inv_implies_powerpm_inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128
    )
        where
            Perm: CheckPermission<Seq<u8>>,
            PMRegion: PersistentMemoryRegion
        requires
            self.inv(powerpm_region)
        ensures
            powerpm_region.inv()
    {}
}

}
