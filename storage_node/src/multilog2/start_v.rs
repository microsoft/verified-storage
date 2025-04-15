#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::invariant;
use vstd::prelude::*;

use super::impl_v::UntrustedMultilogImpl;
use super::inv_v::*;
use super::recover_v::*;
use super::spec_t::*;
use crate::common::align_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::power_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;

verus! {

impl UntrustedMultilogImpl {
    // The `start` static method creates an
    // `UntrustedMultilogImpl` out of a set of persistent memory
    // regions. An assumption is that those regions were initialized
    // with `setup` and then only `UntrustedMultilogImpl` methods
    // were allowed to mutate them. See `README.md` for more
    // documentation and an example of its use.
    //
    // This method is passed a write-restricted collection of
    // persistent memory regions `powerpm_region`. This restricts
    // how we can write `powerpm_region`. This is moot, though,
    // because we don't ever write to the memory.
    pub exec fn start<Perm, PMRegion>(
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        multilog_id: u128,
        Tracked(perm): Tracked<&Perm>,
        Ghost(state): Ghost<RecoveredMultilogState>,
    ) -> (result: Result<Self, MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            old(powerpm_region).inv(),
            old(powerpm_region)@.valid(),
            old(powerpm_region)@.flush_predicted(),
            Self::recover(old(powerpm_region)@.durable_state) == Some(state),
            forall|s| #[trigger] perm.check_permission(s) <== Self::recover(s) == Some(state),
        ensures
            powerpm_region.inv(),
            powerpm_region.constants() == old(powerpm_region).constants(),
            match result {
                Ok(log_impl) => {
                    &&& log_impl.valid(powerpm_region)
                    &&& log_impl@.c.id == multilog_id
                    &&& log_impl@.recover() == state
                    &&& log_impl@.tentative == log_impl@.durable
                    &&& Self::recover(powerpm_region@.durable_state) == Some(state)
                },
                Err(
                    MultilogErr::StartFailedDueToMultilogIDMismatch {
                        multilog_id_expected,
                        multilog_id_read,
                    },
                ) => {
                    &&& multilog_id_expected == multilog_id
                    &&& multilog_id_read == state.c.id
                },
                Err(
                    MultilogErr::CRCMismatch,
                ) => !powerpm_region.constants().impervious_to_corruption(),
                _ => false,
            },
    {
        broadcast use pmcopy_axioms;

        let ghost rm = MultilogRecoveryMapping::new(powerpm_region@.durable_state).unwrap();
        assert(rm.corresponds(powerpm_region@.durable_state));

        let pm_region = powerpm_region.get_pm_region_ref();
        let vm = match exec_recover_object::<PMRegion, MultilogVersionMetadata>(
            pm_region,
            0,
            size_of::<MultilogVersionMetadata>() as u64,
        ) {
            Some(vm) => vm,
            None => {
                return Err(MultilogErr::CRCMismatch);
            },
        };
        assert(recover_version_metadata(pm_region@.durable_state) == Some(vm));
        assert(vm == rm.vm);

        let sm = match exec_recover_object::<PMRegion, MultilogStaticMetadata>(
            pm_region,
            vm.static_metadata_addr,
            vm.static_metadata_addr + size_of::<MultilogStaticMetadata>() as u64,
        ) {
            Some(sm) => sm,
            None => {
                return Err(MultilogErr::CRCMismatch);
            },
        };
        assert(recover_static_metadata(pm_region@.durable_state, vm) == Some(sm));
        assert(sm == rm.sm);

        if sm.id != multilog_id {
            return Err(
                MultilogErr::StartFailedDueToMultilogIDMismatch {
                    multilog_id_expected: multilog_id,
                    multilog_id_read: sm.id,
                },
            );
        }
        let mask_cdb = match exec_recover_cdb::<PMRegion>(pm_region, sm.mask_cdb_addr) {
            Some(b) => b,
            None => {
                return Err(MultilogErr::CRCMismatch);
            },
        };
        assert(mask_cdb == rm.mask_cdb);
        let mask_addr = if mask_cdb {
            sm.mask1_addr
        } else {
            sm.mask0_addr
        };
        let mask_crc_addr = if mask_cdb {
            sm.mask1_crc_addr
        } else {
            sm.mask0_crc_addr
        };
        let mask = match exec_recover_object::<PMRegion, u64>(pm_region, mask_addr, mask_crc_addr) {
            Some(mask) => mask,
            None => {
                return Err(MultilogErr::CRCMismatch);
            },
        };
        assert(recover_mask_given_cdb(pm_region@.durable_state, sm, mask_cdb) == Some(mask));
        assert(mask == rm.mask);

        let mut log_infos = Vec::<LogInfo>::new();
        let mut which_log = 0u64;
        while which_log < sm.num_logs
            invariant
                log_infos.len() == which_log,
                powerpm_region.inv(),
                powerpm_region@.valid(),
                powerpm_region@.flush_predicted(),
                Self::recover(powerpm_region@.durable_state) == Some(state),
                pm_region@ == powerpm_region@,
                pm_region.inv(),
                pm_region@.valid(),
                pm_region@.flush_predicted(),
                powerpm_region.constants() == old(powerpm_region).constants(),
                powerpm_region.constants() == pm_region.constants(),
                0 <= which_log <= sm.num_logs,
                forall|i: int|
                    #![trigger log_infos@[i]]
                    #![trigger state.state.logs[i]]
                    0 <= i < which_log ==> {
                        let info = log_infos@[i];
                        let durable = state.state.logs[i];
                        &&& Self::inv_durable_metadata(info, durable)
                        &&& Self::inv_tentative_metadata(info, durable)
                        &&& info.log_area_start == rm.all_log_constants[i].log_area_start
                        &&& info.log_area_len ==
                            rm.all_log_constants[i].log_area_end - rm.all_log_constants[i].log_area_start
                    },
                rm.corresponds(pm_region@.durable_state),
                rm.vm == vm,
                rm.sm == sm,
                rm.mask_cdb == mask_cdb,
                rm.mask == mask,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;

            }

            let row_addr = sm.log_metadata_table.row_index_to_addr(which_log as u64);
            assert(recover_single_log_constants(pm_region@.durable_state, which_log as int, sm)
                == Some(rm.all_log_constants[which_log as int]));
            let c = match exec_recover_object::<PMRegion, SingleLogConstants>(
                pm_region,
                row_addr + sm.log_metadata_row_constants_addr,
                row_addr + sm.log_metadata_row_constants_crc_addr,
            ) {
                Some(c) => c,
                None => {
                    return Err(MultilogErr::CRCMismatch);
                },
            };
            assert(c == rm.all_log_constants[which_log as int]);

            let which_dynamic_metadata = mask & (1u64 << which_log) != 0;
            let dynamic_metadata_addr = if which_dynamic_metadata {
                sm.log_metadata_row_dynamic_metadata1_addr
            } else {
                sm.log_metadata_row_dynamic_metadata0_addr
            };
            let dynamic_metadata_crc_addr = if which_dynamic_metadata {
                sm.log_metadata_row_dynamic_metadata1_crc_addr
            } else {
                sm.log_metadata_row_dynamic_metadata0_crc_addr
            };
            assert(recover_single_log_dynamic_metadata_given_mask(
                pm_region@.durable_state,
                which_log as int,
                sm,
                mask,
            ) == Some(rm.all_log_dynamic_metadata[which_log as int]));
            let d = match exec_recover_object::<PMRegion, SingleLogDynamicMetadata>(
                pm_region,
                row_addr + dynamic_metadata_addr,
                row_addr + dynamic_metadata_crc_addr,
            ) {
                Some(d) => d,
                None => {
                    return Err(MultilogErr::CRCMismatch);
                },
            };
            assert(d == rm.all_log_dynamic_metadata[which_log as int]);

            let log_area_len = c.log_area_end - c.log_area_start;
            let head_addr = c.log_area_start + (d.head % (log_area_len as u128)) as u64;
            assert(head_addr == c.log_area_start as int + (d.head as int % log_area_len as int));
            let log_info = LogInfo {
                log_area_start: c.log_area_start,
                log_area_end: c.log_area_end,
                log_area_len,
                durable_head: d.head,
                durable_head_addr: head_addr,
                durable_log_length: d.length,
                tentative_head: d.head,
                tentative_head_addr: head_addr,
                tentative_log_length: d.length,
            };

            let ghost durable = state.state.logs[which_log as int];
            assert(log_info.log_area_start
                == rm.all_log_constants[which_log as int].log_area_start);
            assert(log_info.log_area_len == rm.all_log_constants[which_log as int].log_area_end
                - rm.all_log_constants[which_log as int].log_area_start);
            assert(log_info.durable_head == durable.head);
            assert(log_info.durable_log_length == durable.log.len());
            assert(log_info.durable_head_addr == log_info.log_area_start + (durable.head % (
            log_info.log_area_len as int)));
            assert(log_info.tentative_head == durable.head);
            assert(log_info.tentative_log_length == durable.log.len());
            assert(log_info.tentative_head_addr == log_info.log_area_start + (durable.head % (
            log_info.log_area_len as int)));

            log_infos.push(log_info);
            which_log = which_log + 1;
        }

        let ghost mv = MultilogView { c: rm@.c, durable: rm@.state, tentative: rm@.state };
        let result = Self {
            status: Ghost(MultilogStatus::Quiescent),
            vm: Ghost(vm),
            sm,
            log_infos,
            logs_modified: Vec::<u64>::new(),
            durable_mask_cdb: mask_cdb,
            durable_mask: mask,
            rm: Ghost(rm),
            mv: Ghost(mv),
        };

        assert forall|i: int|
            #![trigger result.log_infos@[i]]
            0 <= i < result.sm.num_logs && !result.logs_modified@.contains(i as u64) implies {
            let info = result.log_infos@[i];
            &&& info.durable_head == info.tentative_head
            &&& info.durable_head_addr == info.tentative_head_addr
            &&& info.durable_log_length == info.tentative_log_length
        } by {}

        Ok(result)
    }
}

} // verus!
