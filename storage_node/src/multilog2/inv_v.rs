#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::impl_v::*;
use super::recover_v::*;
use super::spec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;

verus! {

impl LogInfo {
    pub(super) open(super) spec fn durable_atomic_log_state(self) -> AtomicLogState
    {
        AtomicLogState {
            head: self.durable_head as int,
            log: self.durable_log@
        }
    }

    pub(super) open(super) spec fn tentative_atomic_log_state(self) -> AtomicLogState
    {
        AtomicLogState {
            head: self.tentative_head as int,
            log: self.tentative_log@
        }
    }

    pub(super) open(super) spec fn inv(self) -> bool
    {
        &&& self.log_area_end == self.log_area_start + self.log_area_len
        &&& self.durable_log_length == self.durable_log@.len()
        &&& self.durable_head_addr == self.log_area_start + (self.durable_head as int) % (self.log_area_len as int)
        &&& self.durable_log_length <= self.log_area_len
        &&& self.log_area_start <= self.durable_head_addr < self.log_area_end
        &&& self.tentative_log_length == self.tentative_log@.len()
        &&& self.tentative_head_addr == self.log_area_start + (self.tentative_head as int) % (self.log_area_len as int)
        &&& self.tentative_log_length <= self.log_area_len
        &&& self.log_area_start <= self.tentative_head_addr < self.log_area_end
    }

    pub(super) open(super) spec fn durable_matches_tentative(self) -> bool
    {
        &&& self.durable_head == self.tentative_head
        &&& self.durable_head_addr == self.tentative_head_addr
        &&& self.durable_log_length == self.tentative_log_length
        &&& self.durable_log@ == self.tentative_log@
    }

    pub(super) open(super) spec fn consistent_with_recovery_mapping(
        self,
        which_log: int,
        rm: LogRecoveryMapping
    ) -> bool
    {
        &&& self.which_log@ == which_log
        &&& self.log_area_start == rm.c.log_area_start
        &&& self.log_area_end == rm.c.log_area_end
        &&& self.durable_head == rm.dynamic_metadata.head
        &&& self.durable_log_length == rm.dynamic_metadata.length
        &&& self.durable_log@ == rm.log
    }

    pub(super) open(super) spec fn consistent_with_storage_state(
        self,
        durable_state: Seq<u8>,
        read_state: Seq<u8>,
    ) -> bool {
        &&& self.durable_log@ == extract_log_given_metadata_values(
            durable_state,
            self.log_area_start as int,
            self.log_area_end as int,
            self.durable_log_length as int,
            self.durable_head as int
        )
        &&& self.durable_log@ == extract_log_given_metadata_values(
            read_state,
            self.log_area_start as int,
            self.log_area_end as int,
            self.durable_log_length as int,
            self.durable_head as int
        )
        &&& self.tentative_log@ == extract_log_given_metadata_values(
            read_state,
            self.log_area_start as int,
            self.log_area_end as int,
            self.tentative_log_length as int,
            self.tentative_head as int
        )
    }
}

#[verifier::ext_equal]
pub(super) struct UntrustedMultilogInternalView
{
    pub(super) status: MultilogStatus,
    pub(super) vm: MultilogVersionMetadata,
    pub(super) sm: MultilogStaticMetadata,
    pub(super) log_infos: Seq<LogInfo>,
    pub(super) logs_modified: Seq<u64>,
    pub(super) durable_mask_cdb: bool,
    pub(super) durable_mask: u64,
    pub(super) rm: MultilogRecoveryMapping,
}

impl UntrustedMultilogInternalView
{
    pub(super) open(super) spec fn view(self) -> MultilogView
    {
        let c = MultilogConstants{
            id: self.sm.id,
            capacities: Seq::<u64>::new(
                self.sm.num_logs as nat,
                |i: int| (self.log_infos[i].log_area_end - self.log_infos[i].log_area_start) as u64
            )
        };
        let durable = AtomicMultilogState {
            logs: Seq::<AtomicLogState>::new(self.sm.num_logs as nat,
                                             |i: int| self.log_infos[i].durable_atomic_log_state())
        };
        let tentative = AtomicMultilogState {
            logs: Seq::<AtomicLogState>::new(self.sm.num_logs as nat,
                                             |i: int| self.log_infos[i].tentative_atomic_log_state())
        };
        MultilogView {
            c,
            durable,
            tentative,
        }
    }

    pub(super) open(super) spec fn inv_recovery_mapping_consistent_with_other_fields(self) -> bool
    {
        &&& self.rm.vm == self.vm
        &&& self.rm.sm == self.sm
        &&& self.rm.mask_cdb == self.durable_mask_cdb
        &&& self.rm.mask == self.durable_mask
        &&& forall|i: int| #![trigger self.log_infos[i]] #![trigger self.rm.logs[i]]
            0 <= i < self.sm.num_logs ==>
                self.log_infos[i].consistent_with_recovery_mapping(i, self.rm.logs[i])
    }

    pub(super) open(super) spec fn inv_logs_unmodified(self) -> bool {
        &&& forall|i: int| 0 <= i < self.logs_modified.len() ==> 0 <= #[trigger] self.logs_modified[i] < self.sm.num_logs
        &&& forall|i: int| #![trigger self.log_infos[i]]
            0 <= i < self.sm.num_logs && !self.logs_modified.contains(i as u64) ==>
                self.log_infos[i].durable_matches_tentative()
    }

    pub(super) open(super) spec fn inv_state_correspondence(
        self,
        durable_state: Seq<u8>,
        read_state: Seq<u8>,
    ) -> bool {
        &&& forall|i: int|
            #![trigger self.log_infos[i]]
            0 <= i < self.sm.num_logs ==> self.log_infos[i].consistent_with_storage_state(durable_state, read_state)
    }

    pub open(super) spec fn inv_internal(self) -> bool
    {
        &&& self.log_infos.len() == self.sm.num_logs
        &&& self.inv_recovery_mapping_consistent_with_other_fields()
        &&& self.inv_logs_unmodified()
    }

    pub open(super) spec fn inv(self, durable_state: Seq<u8>, read_state: Seq<u8>) -> bool
    {
        &&& self.inv_internal()
        &&& self.rm.corresponds(durable_state)
        &&& self.inv_state_correspondence(durable_state, read_state)
    }
}

impl UntrustedMultilogImpl {
    pub(super) open(super) spec fn internal_view(self) -> UntrustedMultilogInternalView
    {
        UntrustedMultilogInternalView {
            status: self.status@,
            vm: self.vm@,
            sm: self.sm,
            log_infos: self.log_infos@,
            logs_modified: self.logs_modified@,
            durable_mask_cdb: self.durable_mask_cdb,
            durable_mask: self.durable_mask,
            rm: self.rm@,
        }
    }

    pub open(super) spec fn valid<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& self.status@ is Quiescent
        &&& self.inv(powerpm_region)
    }

    pub open(super) spec fn inv<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> bool where Perm: CheckPermission<Seq<u8>>, PMRegion: PersistentMemoryRegion {
        &&& powerpm_region.inv()
        &&& self.internal_view().inv(powerpm_region@.durable_state, powerpm_region@.read_state)
        &&& self.rm@.corresponds(powerpm_region@.durable_state)
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
        assert(self.internal_view()@.recover() =~= self.rm@@);
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
