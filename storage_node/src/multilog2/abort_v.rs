#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::invariant;
use vstd::prelude::*;

use super::impl_v::*;
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
    exec fn revert_log_info_to_durable(&mut self)
        ensures
            self == (Self{ log_infos: self.log_infos, ..*old(self) }),
            self.log_infos@.len() == old(self).log_infos@.len(),
            forall|i: int| #![trigger self.log_infos@[i]]
                0 <= i < self.log_infos@.len() ==> {
                let v1 = old(self).log_infos[i];
                let v2 = self.log_infos[i];
                &&& v2.log_area_start == v1.log_area_start
                &&& v2.log_area_len == v1.log_area_len
                &&& v2.log_area_end == v1.log_area_end
                &&& v2.durable_head == v1.durable_head
                &&& v2.durable_head_addr == v1.durable_head_addr
                &&& v2.durable_log_length == v1.durable_log_length
                &&& v2.tentative_head == v1.durable_head
                &&& v2.tentative_head_addr == v1.durable_head_addr
                &&& v2.tentative_log_length == v1.durable_log_length
            },
    {
        let num_logs = self.log_infos.len();
        for which_log in 0..num_logs
            invariant
                num_logs == self.log_infos.len(),
                self == (Self{ log_infos: self.log_infos, ..*old(self) }),
                forall|i: int| #![trigger self.log_infos@[i]]
                    0 <= i < which_log ==> {
                    let v1 = old(self).log_infos[i];
                    let v2 = self.log_infos[i];
                    &&& v2.log_area_start == v1.log_area_start
                    &&& v2.log_area_len == v1.log_area_len
                    &&& v2.log_area_end == v1.log_area_end
                    &&& v2.durable_head == v1.durable_head
                    &&& v2.durable_head_addr == v1.durable_head_addr
                    &&& v2.durable_log_length == v1.durable_log_length
                    &&& v2.tentative_head == v1.durable_head
                    &&& v2.tentative_head_addr == v1.durable_head_addr
                    &&& v2.tentative_log_length == v1.durable_log_length
                },
                forall|i: int| #![trigger self.log_infos@[i]]
                    which_log <= i < self.log_infos@.len() ==>
                    self.log_infos@[i] == old(self).log_infos@[i],
        {
            let old_info = &self.log_infos[which_log];
            let new_info = LogInfo{
                tentative_head: old_info.durable_head,
                tentative_head_addr: old_info.durable_head_addr,
                tentative_log_length: old_info.durable_log_length,
                ..*old_info
            };
            self.log_infos[which_log] = new_info;
        }
    }

    pub exec fn abort<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
        requires
            old(self).valid(&*old(powerpm_region)),
            forall|s| #[trigger]
                perm.check_permission(s) <== Self::recover(s) == Some(old(self)@.recover()),
        ensures
            self.valid(powerpm_region),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
            powerpm_region.constants() == old(powerpm_region).constants(),
            result is Ok,
            self@ == old(self)@.abort(),
    {
        self.revert_log_info_to_durable();
        self.logs_modified.clear();

        proof {
            self.lemma_inv_implies_can_only_crash_as(powerpm_region);
        }

        Ok(())
    }
}

} // verus!
