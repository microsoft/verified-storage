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

proof fn lemma_bit_set_or_clear_works(
    old_mask: u64,
    new_mask: u64,
    which_bit: u64,
    value: bool
)
    requires
        0 <= which_bit < 64,
        value ==> new_mask == old_mask | (1u64 << which_bit),
        !value ==> new_mask == old_mask & !(1u64 << which_bit),
    ensures
        value <==> mask_bit_set(new_mask, which_bit),
        forall|i: u64| 0 <= i < 64 && i != which_bit ==> {
            mask_bit_set(old_mask, i) == mask_bit_set(new_mask, i)
        },
{
    let new_mask = if value { old_mask | (1u64 << which_bit) } else { old_mask & !(1u64 << which_bit) };
    if value {
        assert(0 <= which_bit < 64 ==> (old_mask | (1u64 << which_bit)) & (1u64 << which_bit) != 0) by (bit_vector);
    }
    else {
        assert(0 <= which_bit < 64 ==> (old_mask & !(1u64 << which_bit)) & (1u64 << which_bit) == 0) by (bit_vector);
    }
    assert forall|i: u64| 0 <= i < 64 && i != which_bit implies mask_bit_set(old_mask, i) == mask_bit_set(new_mask, i) by {
        if value {
            assert(0 <= which_bit < 64 && i != which_bit ==>
                   (old_mask | (1u64 << which_bit)) & (1u64 << i) == old_mask & (1u64 << i)) by (bit_vector);
        }
        else {
            assert(0 <= which_bit < 64 && i != which_bit ==>
                   (old_mask & !(1u64 << which_bit)) & (1u64 << i) == old_mask & (1u64 << i)) by (bit_vector);
        }
    }
}

#[inline]
exec fn bit_set_or_clear(old_mask: u64, which_bit: u64, value: bool) -> (new_mask: u64)
    requires
        0 <= which_bit < 64,
    ensures
        value <==> mask_bit_set(new_mask, which_bit),
        forall|i: u64| 0 <= i < 64 && i != which_bit ==> {
            mask_bit_set(old_mask, i) == mask_bit_set(new_mask, i)
        },
{
    let new_mask = if value { old_mask | (1u64 << which_bit) } else { old_mask & !(1u64 << which_bit) };
    proof {
        lemma_bit_set_or_clear_works(old_mask, new_mask, which_bit, value);
    }
    new_mask
}

impl UntrustedMultilogImpl {
    exec fn compute_new_mask<Perm, PMRegion>(
        &self,
        powerpm_region: &PoWERPersistentMemoryRegion<Perm, PMRegion>,
    ) -> (new_mask: u64) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
        requires
            self.inv(powerpm_region),
        ensures
            forall|i: u64| #![trigger self.logs_modified@.contains(i)]
                0 <= i < self.sm.num_logs ==>
                (self.logs_modified@.contains(i) <==>
                 mask_bit_set(new_mask, i) != mask_bit_set(self.durable_mask, i)),
    {
        let mut new_mask = self.durable_mask;
        let num_modified_logs = self.logs_modified.len();
        for pos in 0..num_modified_logs
            invariant
                num_modified_logs == self.logs_modified.len(),
                self.inv(powerpm_region),
                forall|i: int| 0 <= i < pos ==> {
                    #[trigger] mask_bit_set(new_mask, self.logs_modified[i]) !=
                    mask_bit_set(self.durable_mask, self.logs_modified[i])
                },
                forall|i: u64| #![trigger self.logs_modified@.contains(i)]
                    0 <= i < self.sm.num_logs && !self.logs_modified@.contains(i) ==>
                    mask_bit_set(new_mask, i) == mask_bit_set(self.durable_mask, i),
        {
            let which_log = self.logs_modified[pos];
            let old_value = (self.durable_mask & (1u64 << which_log as u64)) != 0;
            new_mask = bit_set_or_clear(new_mask, which_log as u64, !old_value);
        }
        new_mask
    }

    exec fn advance_log_info_to_tentative(&mut self)
        ensures
            self == (Self{ log_infos: self.log_infos, ..*old(self) }),
            self.log_infos@.len() == old(self).log_infos@.len(),
            forall|i: int| #![trigger self.log_infos@[i]]
                0 <= i < self.log_infos@.len() ==> {
                let v1 = old(self).log_infos[i];
                let v2 = self.log_infos[i];
                &&& v2.log_area_start == v1.log_area_start
                &&& v2.log_area_len == v1.log_area_len
                &&& v2.durable_head == v1.tentative_head
                &&& v2.durable_head_addr == v1.tentative_head_addr
                &&& v2.durable_log_length == v1.tentative_log_length
                &&& v2.tentative_head == v1.tentative_head
                &&& v2.tentative_head_addr == v1.tentative_head_addr
                &&& v2.tentative_log_length == v1.tentative_log_length
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
                    &&& v2.durable_head == v1.tentative_head
                    &&& v2.durable_head_addr == v1.tentative_head_addr
                    &&& v2.durable_log_length == v1.tentative_log_length
                    &&& v2.tentative_head == v1.tentative_head
                    &&& v2.tentative_head_addr == v1.tentative_head_addr
                    &&& v2.tentative_log_length == v1.tentative_log_length
                },
                forall|i: int| #![trigger self.log_infos@[i]]
                    which_log <= i < self.log_infos@.len() ==>
                    self.log_infos@[i] == old(self).log_infos@[i],
        {
            let old_info = &self.log_infos[which_log];
            let new_info = LogInfo{
                durable_head: old_info.tentative_head,
                durable_head_addr: old_info.tentative_head_addr,
                durable_log_length: old_info.tentative_log_length,
                ..*old_info
            };
            self.log_infos[which_log] = new_info;
        }
    }

    pub exec fn commit<Perm, PMRegion>(
        &mut self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
    ) -> (result: Result<(), MultilogErr>) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,

        requires
            old(self).valid(&*old(powerpm_region)),
            forall|s| #[trigger]
                perm.check_permission(s) <==> {
                    ||| Self::recover(s) == Some(old(self)@.recover())
                    ||| Self::recover(s) == Some(old(self)@.commit().recover())
                },
        ensures
            self.valid(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            result is Ok,
            self@ == old(self)@.commit(),
    {
        self.advance_log_info_to_tentative();
        self.logs_modified.clear();
        self.mv = Ghost(self.mv@.commit());

        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }
}

} // verus!
