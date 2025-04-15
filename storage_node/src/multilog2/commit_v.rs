#![allow(unused_imports)]
use std::ops::Mul;

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

    proof fn lemma_updating_inactive_dynamic_metadata_doesnt_affect_recovery(
        rm: MultilogRecoveryMapping,
        s1: Seq<u8>,
        s2: Seq<u8>,
        which_log: u64,
    )
        requires
            0 <= which_log < rm.sm.num_logs,
            rm.corresponds(s1),
            ({
                let row_addr = rm.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
                let version = !mask_bit_set(rm.mask, which_log);
                let dynamic_metadata_offset = if version {
                    rm.sm.log_metadata_row_dynamic_metadata1_addr
                } else {
                    rm.sm.log_metadata_row_dynamic_metadata0_addr
                };
                let dynamic_metadata_crc_offset = if version {
                    rm.sm.log_metadata_row_dynamic_metadata1_crc_addr
                } else {
                    rm.sm.log_metadata_row_dynamic_metadata0_crc_addr
                };
                seqs_match_except_in_range(s1, s2, row_addr + dynamic_metadata_offset,
                                           row_addr + dynamic_metadata_crc_offset + u64::spec_size_of())
            }),
        ensures
            rm.corresponds(s2),
            Self::recover(s1) == Self::recover(s2),
    {
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        let row_addr = rm.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
        assert(rm.sm.log_metadata_table.validate_row_addr(row_addr));

        let version = !mask_bit_set(rm.mask, which_log);
        let dynamic_metadata_offset = if version {
            rm.sm.log_metadata_row_dynamic_metadata1_addr
        } else {
            rm.sm.log_metadata_row_dynamic_metadata0_addr
        };
        let dynamic_metadata_crc_offset = if version {
            rm.sm.log_metadata_row_dynamic_metadata1_crc_addr
        } else {
            rm.sm.log_metadata_row_dynamic_metadata0_crc_addr
        };

        assert(rm.corresponds(s2));
        rm.lemma_corresponds_implies_equals_new(s1);
        rm.lemma_corresponds_implies_equals_new(s2);
    }

    proof fn lemma_updating_inactive_dynamic_metadata_doesnt_affect_inv_state_correspondence(
        self: Self,
        old_durable_state: Seq<u8>,
        old_read_state: Seq<u8>,
        new_durable_state: Seq<u8>,
        new_read_state: Seq<u8>,
        which_log: u64,
    )
        requires
            self.inv_internal(),
            self.rm@.corresponds(old_durable_state),
            self.inv_state_correspondence(old_durable_state, old_read_state),
            old_durable_state.len() == old_read_state.len(),
            0 <= which_log < self.sm.num_logs,
            ({
                let row_addr = self.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
                let version = !mask_bit_set(self.durable_mask, which_log);
                let dynamic_metadata_offset = if version {
                    self.sm.log_metadata_row_dynamic_metadata1_addr
                } else {
                    self.sm.log_metadata_row_dynamic_metadata0_addr
                };
                let dynamic_metadata_crc_offset = if version {
                    self.sm.log_metadata_row_dynamic_metadata1_crc_addr
                } else {
                    self.sm.log_metadata_row_dynamic_metadata0_crc_addr
                };
                &&& seqs_match_except_in_range(old_durable_state, new_durable_state,
                                              row_addr + dynamic_metadata_offset,
                                              row_addr + dynamic_metadata_crc_offset + u64::spec_size_of())
                &&& seqs_match_except_in_range(old_read_state, new_read_state,
                                              row_addr + dynamic_metadata_offset,
                                              row_addr + dynamic_metadata_crc_offset + u64::spec_size_of())
            }),
        ensures
            self.inv_state_correspondence(new_durable_state, new_read_state),
    {
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        let row_addr = self.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
        assert(self.sm.log_metadata_table.validate_row_addr(row_addr));

        let version = !mask_bit_set(self.durable_mask, which_log);
        let dynamic_metadata_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_addr
        };
        let dynamic_metadata_crc_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_crc_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_crc_addr
        };

        assert forall|i: int|
            #![trigger self.log_infos@[i]]
            #![trigger self.mv@.durable.logs[i]]
            0 <= i < self.sm.num_logs implies self.inv_state_corresponds_for_log(new_durable_state,
                                                                                new_read_state, i) by {
            let info = self.log_infos@[i];
            assert(info.durable_log_length <= info.log_area_len);
            assert(info.log_area_len > 0);

            let old_head_addr = info.log_area_start + (info.durable_head as int % info.log_area_len as int);
            assert(row_addr + dynamic_metadata_crc_offset + u64::spec_size_of() <= old_head_addr);
            assert(info.log_area_start + info.log_area_len <= old_read_state.len());

            let new_head_addr = info.log_area_start + (info.tentative_head as int % info.log_area_len as int);
            assert(row_addr + dynamic_metadata_crc_offset + u64::spec_size_of() <= new_head_addr);
            assert(info.log_area_start + info.log_area_len <= new_read_state.len());

                /*
            assert(recover_log_given_metadata(old_durable_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int) ==
                   recover_log_given_metadata(new_durable_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int));
            assert(recover_log_given_metadata(old_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int) ==
                   recover_log_given_metadata(new_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int));
            assert(recover_log_given_metadata(old_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.tentative_log_length as int,
                                              info.tentative_head as int) ==
                   recover_log_given_metadata(new_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.tentative_log_length as int,
                                              info.tentative_head as int));
                */
        }
    }

    proof fn lemma_updating_inactive_dynamic_metadata_doesnt_affect_other_inactive_dynamic_metadata(
        self: Self,
        old_durable_state: Seq<u8>,
        old_read_state: Seq<u8>,
        new_durable_state: Seq<u8>,
        new_read_state: Seq<u8>,
        which_log: u64,
    )
        requires
            self.inv_internal(),
            self.rm@.corresponds(old_durable_state),
            self.inv_state_correspondence(old_durable_state, old_read_state),
            old_durable_state.len() == old_read_state.len(),
            0 <= which_log < self.sm.num_logs,
            ({
                let row_addr = self.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
                let version = !mask_bit_set(self.durable_mask, which_log);
                let dynamic_metadata_offset = if version {
                    self.sm.log_metadata_row_dynamic_metadata1_addr
                } else {
                    self.sm.log_metadata_row_dynamic_metadata0_addr
                };
                let dynamic_metadata_crc_offset = if version {
                    self.sm.log_metadata_row_dynamic_metadata1_crc_addr
                } else {
                    self.sm.log_metadata_row_dynamic_metadata0_crc_addr
                };
                &&& seqs_match_except_in_range(old_durable_state, new_durable_state,
                                              row_addr + dynamic_metadata_offset,
                                              row_addr + dynamic_metadata_crc_offset + u64::spec_size_of())
                &&& seqs_match_except_in_range(old_read_state, new_read_state,
                                              row_addr + dynamic_metadata_offset,
                                              row_addr + dynamic_metadata_crc_offset + u64::spec_size_of())
            }),
        ensures
            forall|i: int| #![trigger self.log_infos@[i]]
                0 <= i < self.log_infos@.len() && i != which_log ==>
                recover_single_log_dynamic_metadata_given_version(
                    new_read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ) ==
                recover_single_log_dynamic_metadata_given_version(
                    old_read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ),
    {
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
//        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        let row_addr = self.sm.log_metadata_table.spec_row_index_to_addr(which_log as int);
        assert(self.sm.log_metadata_table.validate_row_addr(row_addr));

        let version = !mask_bit_set(self.durable_mask, which_log);
        let dynamic_metadata_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_addr
        };
        let dynamic_metadata_crc_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_crc_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_crc_addr
        };

        assert forall|i: int| #![trigger self.log_infos@[i]]
                0 <= i < self.log_infos@.len() && i != which_log implies
                recover_single_log_dynamic_metadata_given_version(
                    new_read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ) ==
                recover_single_log_dynamic_metadata_given_version(
                    old_read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ) by {
            let info = self.log_infos@[i];
            assert(info.durable_log_length <= info.log_area_len);
            assert(info.log_area_len > 0);

            let head_addr = info.log_area_start + (info.durable_head as int % info.log_area_len as int);
            assert(row_addr + dynamic_metadata_crc_offset + u64::spec_size_of() <= head_addr);
            assert(info.log_area_start + info.log_area_len <= old_read_state.len());

                    /*
            assert(recover_log_given_metadata(old_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int) ==
                   recover_log_given_metadata(new_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.durable_log_length as int,
                                              info.durable_head as int));
            assert(recover_log_given_metadata(old_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.tentative_log_length as int,
                                              info.tentative_head as int) ==
                   recover_log_given_metadata(new_read_state, info.log_area_start as int,
                                              info.log_area_start + info.log_area_len,
                                              info.tentative_log_length as int,
                                              info.tentative_head as int));
                    */
        }
    }

    #[verifier::rlimit(30)]
    exec fn update_one_log_dynamic_metadata<Perm, PMRegion>(
        &self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        which_log: u64,
    ) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old(powerpm_region)),
            self.logs_modified@.contains(which_log),
            perm.valid(old(powerpm_region).id()),
            forall|s| #[trigger]
                perm.check_permission(s) <== Self::recover(s) == Some(self@.recover()),
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
            forall|i: int| #![trigger self.log_infos@[i]]
                0 <= i < self.log_infos@.len() && i != which_log ==>
                recover_single_log_dynamic_metadata_given_version(
                    powerpm_region@.read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ) ==
                recover_single_log_dynamic_metadata_given_version(
                    old(powerpm_region)@.read_state,
                    which_log as int,
                    self.sm,
                    !mask_bit_set(self.durable_mask, which_log)
                ),
            recover_single_log_dynamic_metadata_given_version(
                powerpm_region@.read_state,
                which_log as int,
                self.sm,
                !mask_bit_set(self.durable_mask, which_log),
            ) == Some(SingleLogDynamicMetadata{
                length: self.log_infos@[which_log as int].tentative_log_length,
                head: self.log_infos@[which_log as int].tentative_head,
            }),
    {
        broadcast use group_update_bytes_effect;
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
        broadcast use pmcopy_axioms;
        broadcast use broadcast_can_result_from_partial_write_effect_on_subranges;

        proof {
            powerpm_region.lemma_inv_implies_view_valid();
            self.lemma_inv_implies_can_only_crash_as(powerpm_region);
        }

        assert(self.rm@.all_log_constants[0].log_area_start <= self.rm@.all_log_constants.last().log_area_end);
        assert(self.sm.log_metadata_table.end <= self.rm@.all_log_constants[which_log as int].log_area_start);

        let row_addr = self.sm.log_metadata_table.row_index_to_addr(which_log);
        assert(row_addr == self.sm.log_metadata_table.spec_row_index_to_addr(which_log as int));

        let version = self.durable_mask & (1u64 << which_log as u64) == 0;
        assert(version == !mask_bit_set(self.durable_mask, which_log));

        let dynamic_metadata_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_addr
        };
        let dynamic_metadata_crc_offset = if version {
            self.sm.log_metadata_row_dynamic_metadata1_crc_addr
        } else {
            self.sm.log_metadata_row_dynamic_metadata0_crc_addr

        };

        let info = &self.log_infos[which_log as usize];
        let d = SingleLogDynamicMetadata{
            length: info.tentative_log_length,
            head: info.tentative_head,
        };
        let d_crc = calculate_crc(&d);

        assert forall |s| can_result_from_partial_write(
            s, powerpm_region@.durable_state, row_addr + dynamic_metadata_offset, d.spec_to_bytes())
            implies #[trigger] perm.check_permission(s) by {
            Self::lemma_updating_inactive_dynamic_metadata_doesnt_affect_recovery(
                self.rm@, powerpm_region@.durable_state, s, which_log
            );
        }

        powerpm_region.serialize_and_write::<SingleLogDynamicMetadata>(
            row_addr + dynamic_metadata_offset,
            &d,
            Tracked(perm),
        );
        proof {
            assert(can_result_from_partial_write(powerpm_region@.durable_state, old(powerpm_region)@.durable_state,
                                                 row_addr + dynamic_metadata_offset, d.spec_to_bytes()));
            Self::lemma_updating_inactive_dynamic_metadata_doesnt_affect_recovery(
                self.rm@, old(powerpm_region)@.durable_state, powerpm_region@.durable_state, which_log
            );
        }

        let ghost mid_contents = powerpm_region@.durable_state;
        assert forall |s| can_result_from_partial_write(
            s, powerpm_region@.durable_state, row_addr + dynamic_metadata_crc_offset, d_crc.spec_to_bytes())
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_can_result_from_partial_write_effect_on_subranges;
            Self::lemma_updating_inactive_dynamic_metadata_doesnt_affect_recovery(
                self.rm@, powerpm_region@.durable_state, s, which_log
            );
        }
        powerpm_region.serialize_and_write::<u64>(
            row_addr + dynamic_metadata_crc_offset,
            &d_crc,
            Tracked(perm)
        );
        proof {
            assert(can_result_from_partial_write(powerpm_region@.durable_state, mid_contents,
                                                 row_addr + dynamic_metadata_crc_offset, d_crc.spec_to_bytes()));
            broadcast use broadcast_can_result_from_partial_write_effect_on_subranges;
            Self::lemma_updating_inactive_dynamic_metadata_doesnt_affect_recovery(
                self.rm@, old(powerpm_region)@.durable_state, powerpm_region@.durable_state, which_log
            );
        }

        assert(recover_single_log_dynamic_metadata_given_version(
            powerpm_region@.read_state,
            which_log as int,
            self.sm,
            version,
        ) =~= Some(d));

        proof {
            self.lemma_updating_inactive_dynamic_metadata_doesnt_affect_inv_state_correspondence(
                old(powerpm_region)@.durable_state,
                old(powerpm_region)@.read_state,
                powerpm_region@.durable_state,
                powerpm_region@.read_state,
                which_log
            );
            self.lemma_updating_inactive_dynamic_metadata_doesnt_affect_other_inactive_dynamic_metadata(
                old(powerpm_region)@.durable_state,
                old(powerpm_region)@.read_state,
                powerpm_region@.durable_state,
                powerpm_region@.read_state,
                which_log
            );
        }
    }

    exec fn update_all_log_dynamic_metadata<Perm, PMRegion>(
        &self,
        powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PMRegion>,
        Tracked(perm): Tracked<&Perm>,
        new_mask: u64,
    ) where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion,
        requires
            self.inv(old(powerpm_region)),
            perm.valid(old(powerpm_region).id()),
            forall|s| #[trigger]
                perm.check_permission(s) <== Self::recover(s) == Some(self@.recover()),
        ensures
            self.inv(powerpm_region),
            powerpm_region.constants() == old(powerpm_region).constants(),
    {
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
                &&& v2.log_area_end == v1.log_area_end
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
                    &&& v2.log_area_end == v1.log_area_end
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
            old(self).valid(old(powerpm_region)),
            perm.valid(old(powerpm_region).id()),
            forall|s| #[trigger]
                perm.check_permission(s) <==> {
                    ||| Self::recover(s) == Some(old(self)@.recover())
                    ||| Self::recover(s) == Some(old(self)@.commit().recover())
                },
        ensures
            self.valid(powerpm_region),
            Self::recover(powerpm_region@.durable_state) == Some(self@.recover()),
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
