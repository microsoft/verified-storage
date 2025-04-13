#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::invariant;
use vstd::prelude::*;

use super::impl_v::UntrustedMultilogImpl;
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
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use vstd::arithmetic::overflow::CheckedU64;

verus! {

pub open(super) spec fn spec_sum_u64s(s: Seq<u64>) -> nat {
    s.fold_left(0nat, |acc: nat, x: u64| (acc + x) as nat)
}

exec fn sum_u64s(v: &Vec<u64>) -> (result: CheckedU64)
    ensures
        result@ == spec_sum_u64s(v@),
{
    let mut result = CheckedU64::new(0u64);
    for n in 0..v.len()
        invariant
            result@ == spec_sum_u64s(v@.take(n as int)),
    {
        result = result.add_value(v[n]);
        assert(v@.take(n + 1).drop_last() =~= v@.take(n as int));
        assert(v@.take(n + 1).last() == v@[n as int]);
    }
    assert(v@.take(v.len() as int) == v@);
    result
}

proof fn lemma_sum_u64s_step(s: Seq<u64>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(s.take(i)) + s[i],
{
    assert(s.take(i + 1).drop_last() =~= s.take(i));
    assert(s.take(i + 1).last() == s[i]);
}

proof fn lemma_sum_u64s_increases(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s.take(j)),
    decreases j - i,
{
    if i < j {
        lemma_sum_u64s_step(s, i);
        lemma_sum_u64s_increases(s, i + 1, j);
    }
}

proof fn lemma_sum_u64s_bound(s: Seq<u64>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_sum_u64s_bound(s, i + 1);
        lemma_sum_u64s_step(s, i);
    } else {
        assert(s.take(i) =~= s);
    }
}

proof fn lemma_sum_u64s_forall(s: Seq<u64>)
    ensures
        forall|i: int|
            0 <= i < s.len() ==> spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(s.take(i))
                + #[trigger] s[i],
        forall|i: int|
            0 <= i <= s.len() ==> #[trigger] spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s),
{
    assert forall|i: int| 0 <= i < s.len() implies spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(
        s.take(i),
    ) + #[trigger] s[i] by {
        lemma_sum_u64s_step(s, i);
    }
    assert forall|i: int| 0 <= i <= s.len() implies #[trigger] spec_sum_u64s(s.take(i))
        <= spec_sum_u64s(s) by {
        lemma_sum_u64s_bound(s, i);
    }
}

impl UntrustedMultilogImpl {
    pub open(super) spec fn spec_space_needed_for_setup(capacities: Seq<u64>) -> nat {
        // First calculate the size of the log metadata table.
        let log_metadata_row_constants_end = SingleLogConstants::spec_size_of();
        let log_metadata_row_constants_crc_end = log_metadata_row_constants_end
            + u64::spec_size_of();
        let log_metadata_row_dynamic_metadata0_end = log_metadata_row_constants_crc_end
            + SingleLogDynamicMetadata::spec_size_of();
        let log_metadata_row_dynamic_metadata0_crc_end = log_metadata_row_dynamic_metadata0_end
            + u64::spec_size_of();
        let log_metadata_row_dynamic_metadata1_end = log_metadata_row_dynamic_metadata0_crc_end
            + SingleLogDynamicMetadata::spec_size_of();
        let log_metadata_row_dynamic_metadata1_crc_end = log_metadata_row_dynamic_metadata1_end
            + u64::spec_size_of();
        let log_metatata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metatata_table_row_size * capacities.len();

        // Next calculate the size needed for the log data.
        let total_capacity: nat = spec_sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = MultilogVersionMetadata::spec_size_of();
        let version_metadata_crc_end = version_metadata_end + u64::spec_size_of();
        let static_metadata_end = version_metadata_crc_end + MultilogStaticMetadata::spec_size_of();
        let static_metadata_crc_end = static_metadata_end + u64::spec_size_of();
        let mask_cdb_start = round_up_to_alignment(
            static_metadata_crc_end as int,
            u64::spec_align_of() as int,
        ) as nat;
        let mask_cdb_end = mask_cdb_start + u64::spec_size_of();
        let mask0_end = mask_cdb_end + u64::spec_size_of();
        let mask0_crc_end = mask0_end + u64::spec_size_of();
        let mask1_end = mask0_crc_end + u64::spec_size_of();
        let mask1_crc_end = mask1_end + u64::spec_size_of();
        let log_metadata_table_end = mask1_crc_end + log_metadata_table_size;
        let log_areas_end = log_metadata_table_end + total_capacity;
        log_areas_end
    }

    pub exec fn space_needed_for_setup(capacities: &Vec<u64>) -> (result: Result<u64, MultilogErr>)
        ensures
            match result {
                Ok(v) => v == Self::spec_space_needed_for_setup(capacities@),
                Err(
                    MultilogErr::SpaceNeededForSetupExceedsMax,
                ) => Self::spec_space_needed_for_setup(capacities@) > u64::MAX,
                Err(_) => false,
            },
    {
        // First calculate the size of the log metadata table.
        let log_metadata_row_constants_end = CheckedU64::new(
            size_of::<SingleLogConstants>() as u64,
        );
        let log_metadata_row_constants_crc_end = log_metadata_row_constants_end.add_value(
            size_of::<u64>() as u64,
        );
        let log_metadata_row_dynamic_metadata0_end = log_metadata_row_constants_crc_end.add_value(
            size_of::<SingleLogDynamicMetadata>() as u64,
        );
        let log_metadata_row_dynamic_metadata0_crc_end =
            log_metadata_row_dynamic_metadata0_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata1_end =
            log_metadata_row_dynamic_metadata0_crc_end.add_value(
            size_of::<SingleLogDynamicMetadata>() as u64,
        );
        let log_metadata_row_dynamic_metadata1_crc_end =
            log_metadata_row_dynamic_metadata1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metadata_table_row_size.mul_value(
            capacities.len() as u64,
        );

        // Next calculate the size needed for the log data.
        let total_capacity = sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = CheckedU64::new(size_of::<MultilogVersionMetadata>() as u64);
        let version_metadata_crc_end = version_metadata_end.add_value(size_of::<u64>() as u64);
        let static_metadata_end = version_metadata_crc_end.add_value(
            size_of::<MultilogStaticMetadata>() as u64,
        );
        let static_metadata_crc_end = static_metadata_end.add_value(size_of::<u64>() as u64);
        let mask_cdb_start = align_checked_u64_to_usize(
            &static_metadata_crc_end,
            align_of::<u64>(),
        );
        let mask_cdb_end = mask_cdb_start.add_value(size_of::<u64>() as u64);
        let mask0_end = mask_cdb_end.add_value(size_of::<u64>() as u64);
        let mask0_crc_end = mask0_end.add_value(size_of::<u64>() as u64);
        let mask1_end = mask0_crc_end.add_value(size_of::<u64>() as u64);
        let mask1_crc_end = mask1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_end = mask1_crc_end.add_checked(&log_metadata_table_size);
        let log_areas_end = log_metadata_table_end.add_checked(&total_capacity);
        assert(log_areas_end@ == Self::spec_space_needed_for_setup(capacities@));

        if log_areas_end.is_overflowed() {
            Err(MultilogErr::SpaceNeededForSetupExceedsMax)
        } else {
            Ok(log_areas_end.unwrap())
        }
    }

    exec fn initialize_log_constants<PMRegion>(
        pm_region: &mut PMRegion,
        vm: Ghost<MultilogVersionMetadata>,
        sm: &MultilogStaticMetadata,
        Ghost(rm): Ghost<MultilogRecoveryMapping>,
        which_log: usize,
        c: &SingleLogConstants,
    ) where PMRegion: PersistentMemoryRegion
        requires
            0 <= which_log < sm.num_logs,
            old(pm_region).inv(),
            old(pm_region)@.valid(),
            rm.valid(),
            rm.all_log_constants.last().log_area_end <= old(pm_region)@.len(),
            rm.vm == vm,
            rm.sm == *sm,
        ensures
            pm_region.inv(),
            pm_region@.valid(),
            pm_region@.len() == old(pm_region)@.len(),
            pm_region.constants() == old(pm_region).constants(),
            recover_version_metadata(pm_region@.read_state) == recover_version_metadata(
                old(pm_region)@.read_state,
            ),
            recover_static_metadata(pm_region@.read_state, vm@) == recover_static_metadata(
                old(pm_region)@.read_state,
                vm@,
            ),
            recover_mask_cdb(pm_region@.read_state, *sm) == recover_mask_cdb(
                old(pm_region)@.read_state,
                *sm,
            ),
            recover_mask_given_cdb(pm_region@.read_state, *sm, rm.mask_cdb)
                == recover_mask_given_cdb(old(pm_region)@.read_state, *sm, rm.mask_cdb),
            forall|i: int|
                0 <= i < sm.num_logs && i != which_log ==> recover_single_log_constants(
                    pm_region@.read_state,
                    i,
                    *sm,
                ) == recover_single_log_constants(old(pm_region)@.read_state, i, *sm),
            recover_single_log_constants(pm_region@.read_state, which_log as int, *sm) == Some(*c),
            forall|i: int|
                0 <= i < sm.num_logs ==> recover_single_log_dynamic_metadata_given_mask(
                    pm_region@.read_state,
                    i,
                    *sm,
                    rm.mask,
                ) == recover_single_log_dynamic_metadata_given_mask(
                    old(pm_region)@.read_state,
                    i,
                    *sm,
                    rm.mask,
                ),
    {
        broadcast use group_update_bytes_effect;
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
        broadcast use pmcopy_axioms;

        assert(rm.all_log_constants[0].log_area_start <= rm.all_log_constants.last().log_area_end);
        assert(sm.log_metadata_table.end <= rm.all_log_constants[which_log as int].log_area_start);

        let row_addr = sm.log_metadata_table.row_index_to_addr(which_log as u64);
        assert(row_addr == sm.log_metadata_table.spec_row_index_to_addr(which_log as int));
        pm_region.serialize_and_write::<SingleLogConstants>(
            row_addr + sm.log_metadata_row_constants_addr,
            &c,
        );
        let c_crc = calculate_crc(c);
        pm_region.serialize_and_write::<u64>(
            row_addr + sm.log_metadata_row_constants_crc_addr,
            &c_crc,
        );

        assert(recover_single_log_constants(pm_region@.read_state, which_log as int, *sm) =~= Some(
            *c,
        ));
        assert(0 <= which_log < 64 ==> 0u64 & (1u64 << which_log) == 0u64) by (bit_vector);
    }

    exec fn update_log_dynamic_metadata<PMRegion>(
        pm_region: &mut PMRegion,
        vm: Ghost<MultilogVersionMetadata>,
        sm: &MultilogStaticMetadata,
        Ghost(rm): Ghost<MultilogRecoveryMapping>,
        which_log: usize,
        d: &SingleLogDynamicMetadata,
        d_crc: u64,
        version: bool,
    ) where PMRegion: PersistentMemoryRegion
        requires
            0 <= which_log < sm.num_logs,
            old(pm_region).inv(),
            old(pm_region)@.valid(),
            rm.valid(),
            rm.all_log_constants.last().log_area_end <= old(pm_region)@.len(),
            rm.vm == vm,
            rm.sm == *sm,
            d_crc == spec_crc_u64(d.spec_to_bytes()),
        ensures
            pm_region.inv(),
            pm_region@.valid(),
            pm_region@.len() == old(pm_region)@.len(),
            pm_region.constants() == old(pm_region).constants(),
            recover_version_metadata(pm_region@.read_state) == recover_version_metadata(
                old(pm_region)@.read_state,
            ),
            recover_static_metadata(pm_region@.read_state, vm@) == recover_static_metadata(
                old(pm_region)@.read_state,
                vm@,
            ),
            recover_mask_cdb(pm_region@.read_state, *sm) == recover_mask_cdb(
                old(pm_region)@.read_state,
                *sm,
            ),
            recover_mask_given_cdb(pm_region@.read_state, *sm, rm.mask_cdb)
                == recover_mask_given_cdb(old(pm_region)@.read_state, *sm, rm.mask_cdb),
            forall|i: int|
                0 <= i < sm.num_logs ==> recover_single_log_constants(pm_region@.read_state, i, *sm)
                    == recover_single_log_constants(old(pm_region)@.read_state, i, *sm),
            forall|i: int|
                0 <= i < sm.num_logs && i != which_log
                    ==> recover_single_log_dynamic_metadata_given_mask(
                    pm_region@.read_state,
                    i,
                    *sm,
                    rm.mask,
                ) == recover_single_log_dynamic_metadata_given_mask(
                    old(pm_region)@.read_state,
                    i,
                    *sm,
                    rm.mask,
                ),
            recover_single_log_dynamic_metadata_given_version(
                pm_region@.read_state,
                which_log as int,
                *sm,
                version,
            ) == Some(*d),
    {
        broadcast use group_update_bytes_effect;
        broadcast use group_validate_row_addr;
        broadcast use lemma_row_index_to_addr_is_valid;
        broadcast use pmcopy_axioms;

        assert(rm.all_log_constants[0].log_area_start <= rm.all_log_constants.last().log_area_end);
        assert(sm.log_metadata_table.end <= rm.all_log_constants[which_log as int].log_area_start);

        let row_addr = sm.log_metadata_table.row_index_to_addr(which_log as u64);
        assert(row_addr == sm.log_metadata_table.spec_row_index_to_addr(which_log as int));
        let dynamic_metadata_offset = if version {
            sm.log_metadata_row_dynamic_metadata1_addr
        } else {
            sm.log_metadata_row_dynamic_metadata0_addr
        };
        let dynamic_metadata_crc_offset = if version {
            sm.log_metadata_row_dynamic_metadata1_crc_addr
        } else {
            sm.log_metadata_row_dynamic_metadata0_crc_addr
        };
        pm_region.serialize_and_write::<SingleLogDynamicMetadata>(
            row_addr + dynamic_metadata_offset,
            d,
        );
        pm_region.serialize_and_write::<u64>(row_addr + dynamic_metadata_crc_offset, &d_crc);

        assert(recover_single_log_dynamic_metadata_given_version(
            pm_region@.read_state,
            which_log as int,
            *sm,
            version,
        ) =~= Some(*d));
    }

    exec fn setup_given_metadata<PMRegion>(
        pm_region: &mut PMRegion,
        capacities: &Vec<u64>,
        vm: &MultilogVersionMetadata,
        sm: &MultilogStaticMetadata,
        Ghost(rm): Ghost<MultilogRecoveryMapping>,
    ) -> (result: Result<(), MultilogErr>) where PMRegion: PersistentMemoryRegion
        requires
            old(pm_region).inv(),
            old(pm_region)@.valid(),
            old(pm_region)@.len() >= sm.log_metadata_table.end + spec_sum_u64s(capacities@),
            old(pm_region)@.len() <= u64::MAX,
            validate_version_metadata(*vm),
            validate_static_metadata(*sm, *vm),
            sm.num_logs == capacities.len(),
            0 < capacities.len() <= MAX_NUM_LOGS,
            forall|i: int| 0 <= i < capacities@.len() ==> #[trigger] capacities@[i] > 0,
            rm.valid(),
            rm.vm == *vm,
            rm.sm == *sm,
            !rm.mask_cdb,
            rm.mask == 0,
            forall|i: int|
                #![trigger rm.all_log_constants[i]]
                0 <= i < sm.num_logs ==> {
                    &&& rm.all_log_constants[i].log_area_start == sm.log_metadata_table.end
                        + spec_sum_u64s(capacities@.take(i))
                    &&& rm.all_log_constants[i].log_area_end == sm.log_metadata_table.end
                        + spec_sum_u64s(capacities@.take(i + 1))
                },
            forall|i: int|
                0 <= i < sm.num_logs ==> #[trigger] rm.all_log_dynamic_metadata[i] == (
                SingleLogDynamicMetadata { head: 0, length: 0 }),
            rm@ == RecoveredMultilogState::initialize(sm.id, capacities@),
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            match result {
                Ok(()) => {
                    let state = RecoveredMultilogState::initialize(sm.id, capacities@);
                    &&& pm_region@.len() == old(pm_region)@.len()
                    &&& pm_region@.flush_predicted()
                    &&& Self::recover(pm_region@.durable_state) == Some(state)
                },
                _ => false,
            },
    {
        broadcast use pmcopy_axioms;
        broadcast use group_update_bytes_effect;

        pm_region.serialize_and_write::<MultilogVersionMetadata>(0, vm);
        let vm_crc = calculate_crc(vm);
        pm_region.serialize_and_write::<u64>(size_of::<MultilogVersionMetadata>() as u64, &vm_crc);
        assert(recover_version_metadata(pm_region@.read_state) == Some(*vm));

        pm_region.serialize_and_write::<MultilogStaticMetadata>(vm.static_metadata_addr, sm);
        let sm_crc = calculate_crc(sm);
        pm_region.serialize_and_write::<u64>(
            vm.static_metadata_addr + size_of::<MultilogStaticMetadata>() as u64,
            &sm_crc,
        );
        assert(recover_static_metadata(pm_region@.read_state, *vm) == Some(*sm));

        let mask_cdb = CDB_FALSE;
        pm_region.serialize_and_write::<u64>(sm.mask_cdb_addr, &mask_cdb);
        let mask = 0u64;
        pm_region.serialize_and_write::<u64>(sm.mask0_addr, &mask);
        let mask_crc = calculate_crc(&mask);
        pm_region.serialize_and_write::<u64>(sm.mask0_crc_addr, &mask_crc);
        assert(!rm.mask_cdb);
        assert(recover_mask_cdb(pm_region@.read_state, *sm) == Some(rm.mask_cdb));
        assert(recover_mask_given_cdb(pm_region@.read_state, *sm, rm.mask_cdb) == Some(0u64));

        let num_logs = capacities.len();
        let mut current_offset = sm.log_metadata_table.end;
        let d = SingleLogDynamicMetadata { length: 0, head: 0 };
        let d_crc = calculate_crc(&d);
        for which_log in 0..num_logs
            invariant
                pm_region.inv(),
                pm_region@.valid(),
                pm_region@.len() >= sm.log_metadata_table.end + spec_sum_u64s(capacities@),
                pm_region@.len() <= u64::MAX,
                pm_region@.len() == old(pm_region)@.len(),
                pm_region.constants() == old(pm_region).constants(),
                validate_version_metadata(*vm),
                validate_static_metadata(*sm, *vm),
                recover_version_metadata(pm_region@.read_state) == Some(*vm),
                recover_static_metadata(pm_region@.read_state, *vm) == Some(*sm),
                recover_mask_cdb(pm_region@.read_state, *sm) == Some(rm.mask_cdb),
                recover_mask_given_cdb(pm_region@.read_state, *sm, rm.mask_cdb) == Some(rm.mask),
                rm.valid(),
                rm.vm == *vm,
                rm.sm == *sm,
                rm@ == RecoveredMultilogState::initialize(sm.id, capacities@),
                !rm.mask_cdb,
                rm.mask == 0,
                forall|i: int|
                    #![trigger rm.all_log_constants[i]]
                    0 <= i < sm.num_logs ==> {
                        &&& rm.all_log_constants[i].log_area_start == sm.log_metadata_table.end
                            + spec_sum_u64s(capacities@.take(i))
                        &&& rm.all_log_constants[i].log_area_end == sm.log_metadata_table.end
                            + spec_sum_u64s(capacities@.take(i + 1))
                    },
                forall|i: int|
                    0 <= i < sm.num_logs ==> #[trigger] rm.all_log_dynamic_metadata[i] == (
                    SingleLogDynamicMetadata { head: 0, length: 0 }),
                forall|i: int|
                    0 <= i < which_log ==> recover_single_log_constants(
                        pm_region@.read_state,
                        i,
                        *sm,
                    ) == Some(#[trigger] rm.all_log_constants[i]),
                current_offset == sm.log_metadata_table.end + spec_sum_u64s(
                    capacities@.take(which_log as int),
                ),
                num_logs == capacities.len() == sm.num_logs,
                d == (SingleLogDynamicMetadata { length: 0, head: 0 }),
                d_crc == spec_crc_u64(d.spec_to_bytes()),
                forall|i: int|
                    0 <= i < which_log ==> recover_single_log_dynamic_metadata_given_mask(
                        pm_region@.read_state,
                        i,
                        *sm,
                        rm.mask,
                    ) == Some(#[trigger] rm.all_log_dynamic_metadata[i]),
                forall|i: int|
                    0 <= i < sm.num_logs ==> #[trigger] rm.all_log_dynamic_metadata[i] == d,
        {
            assert(spec_sum_u64s(capacities@.take(which_log + 1)) == spec_sum_u64s(
                capacities@.take(which_log as int),
            ) + capacities[which_log as int]) by {
                lemma_sum_u64s_step(capacities@, which_log as int);
            }
            assert(spec_sum_u64s(capacities@.take(which_log + 1)) <= spec_sum_u64s(capacities@))
                by {
                lemma_sum_u64s_bound(capacities@, which_log + 1);
            }
            let c = SingleLogConstants {
                log_area_start: current_offset,
                log_area_end: current_offset + capacities[which_log],
            };
            assert(c == rm.all_log_constants[which_log as int]);
            Self::initialize_log_constants(pm_region, Ghost(*vm), sm, Ghost(rm), which_log, &c);
            current_offset = current_offset + capacities[which_log];
            assert(current_offset == sm.log_metadata_table.end + spec_sum_u64s(
                capacities@.take(which_log + 1),
            ));

            Self::update_log_dynamic_metadata(
                pm_region,
                Ghost(*vm),
                sm,
                Ghost(rm),
                which_log,
                &d,
                d_crc,
                false,
            );

            assert(recover_single_log_dynamic_metadata_given_mask(
                pm_region@.read_state,
                which_log as int,
                *sm,
                rm.mask,
            ) =~= Some(d)) by {
                assert(0 <= which_log < 64 ==> 0u64 & (1u64 << which_log) == 0u64) by (bit_vector);
            }
        }

        assert forall |which_log: int| #![trigger rm.state.logs[which_log]]
                   0 <= which_log < rm.sm.num_logs implies
                   rm.state.logs.index(which_log).log ==
                   recover_log(pm_region@.read_state, rm.all_log_constants.index(which_log),
                               rm.all_log_dynamic_metadata.index(which_log)) by {
            assert(recover_log(pm_region@.read_state, rm.all_log_constants.index(which_log),
                               rm.all_log_dynamic_metadata.index(which_log)) =~= Seq::<u8>::empty());
        }

        proof {
            assert(rm.corresponds(pm_region@.read_state));
            rm.lemma_corresponds_implies_equals_new(pm_region@.read_state);
        }

        pm_region.flush();
        Ok(())
    }

    // The `setup` method sets up persistent memory objects `pm_region`
    // to store an initial empty log. It returns the capacity of the log.
    // See `README.md` for more documentation.
    pub exec fn setup<PMRegion>(
        pm_region: &mut PMRegion,
        multilog_id: u128,
        capacities: &Vec<u64>,
    ) -> (result: Result<(), MultilogErr>) where PMRegion: PersistentMemoryRegion
        requires
            old(pm_region).inv(),
            old(pm_region)@.valid(),
        ensures
            pm_region.inv(),
            pm_region.constants() == old(pm_region).constants(),
            match result {
                Ok(()) => {
                    let state = RecoveredMultilogState::initialize(multilog_id, capacities@);
                    &&& pm_region@.len() == old(pm_region)@.len()
                    &&& pm_region@.flush_predicted()
                    &&& Self::recover(pm_region@.durable_state) == Some(state)
                },
                Err(MultilogErr::CantSetupWithFewerThanOneRegion) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& capacities@.len() == 0
                },
                Err(MultilogErr::CantSetupWithMoreThanMaxRegions { max_num_regions }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& capacities@.len() > max_num_regions
                },
                Err(MultilogErr::CapacityMustBePositive { which_log }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& 0 <= which_log < capacities@.len()
                    &&& capacities@[which_log as int] == 0
                },
                Err(MultilogErr::SpaceNeededForSetupExceedsMax) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& Self::spec_space_needed_for_setup(capacities@) > u64::MAX
                },
                Err(MultilogErr::InsufficientSpaceForSetup { required_space }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& pm_region@.len() < required_space
                    &&& required_space == Self::spec_space_needed_for_setup(capacities@)
                },
                _ => false,
            },
    {
        let num_logs = capacities.len();
        if num_logs == 0 {
            return Err(MultilogErr::CantSetupWithFewerThanOneRegion);
        }
        if num_logs > MAX_NUM_LOGS {
            return Err(
                MultilogErr::CantSetupWithMoreThanMaxRegions { max_num_regions: MAX_NUM_LOGS },
            );
        }
        for which_log in 0..num_logs
            invariant
                num_logs == capacities@.len(),
                forall|i: int| 0 <= i < which_log ==> #[trigger] capacities@[i] > 0,
                pm_region == old(pm_region),
                pm_region.inv(),
        {
            if capacities[which_log] == 0 {
                return Err(MultilogErr::CapacityMustBePositive { which_log });
            }
        }

        // First calculate the size of the log metadata table.
        let log_metadata_row_constants_end = CheckedU64::new(
            size_of::<SingleLogConstants>() as u64,
        );
        let log_metadata_row_constants_crc_end = log_metadata_row_constants_end.add_value(
            size_of::<u64>() as u64,
        );
        let log_metadata_row_dynamic_metadata0_end = log_metadata_row_constants_crc_end.add_value(
            size_of::<SingleLogDynamicMetadata>() as u64,
        );
        let log_metadata_row_dynamic_metadata0_crc_end =
            log_metadata_row_dynamic_metadata0_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata1_end =
            log_metadata_row_dynamic_metadata0_crc_end.add_value(
            size_of::<SingleLogDynamicMetadata>() as u64,
        );
        let log_metadata_row_dynamic_metadata1_crc_end =
            log_metadata_row_dynamic_metadata1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metadata_table_row_size.mul_value(
            capacities.len() as u64,
        );
        assert(log_metadata_table_size@ == capacities@.len() * log_metadata_table_row_size@) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                capacities@.len() as int,
                log_metadata_table_row_size@ as int,
            );
        }
        assert(log_metadata_table_size@ >= log_metadata_table_row_size@) by {
            vstd::arithmetic::mul::lemma_mul_ordering(
                capacities@.len() as int,
                log_metadata_table_row_size@ as int,
            );
        }

        // Next calculate the size needed for the log data.
        let total_capacity = sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = CheckedU64::new(size_of::<MultilogVersionMetadata>() as u64);
        let version_metadata_crc_end = version_metadata_end.add_value(size_of::<u64>() as u64);
        let static_metadata_end = version_metadata_crc_end.add_value(
            size_of::<MultilogStaticMetadata>() as u64,
        );
        let static_metadata_crc_end = static_metadata_end.add_value(size_of::<u64>() as u64);
        let mask_cdb_start = align_checked_u64_to_usize(
            &static_metadata_crc_end,
            align_of::<u64>(),
        );
        let mask_cdb_end = mask_cdb_start.add_value(size_of::<u64>() as u64);
        let mask0_end = mask_cdb_end.add_value(size_of::<u64>() as u64);
        let mask0_crc_end = mask0_end.add_value(size_of::<u64>() as u64);
        let mask1_end = mask0_crc_end.add_value(size_of::<u64>() as u64);
        let mask1_crc_end = mask1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_end = mask1_crc_end.add_checked(&log_metadata_table_size);
        let log_areas_end = log_metadata_table_end.add_checked(&total_capacity);
        assert(log_areas_end@ == Self::spec_space_needed_for_setup(capacities@));

        if log_areas_end.is_overflowed() {
            return Err(MultilogErr::SpaceNeededForSetupExceedsMax);
        }
        let required_space = log_areas_end.unwrap();
        if required_space > pm_region.get_region_size() {
            return Err(MultilogErr::InsufficientSpaceForSetup { required_space });
        }
        let vm = MultilogVersionMetadata {
            program_guid: MULTILOG_PROGRAM_GUID,
            version_number: MULTILOG_PROGRAM_VERSION_NUMBER,
            static_metadata_addr: version_metadata_crc_end.unwrap(),
        };
        assert(validate_version_metadata(vm));

        let log_metadata_table = TableMetadata::new(
            mask1_crc_end.unwrap(),
            log_metadata_table_end.unwrap(),
            num_logs as u64,
            log_metadata_table_row_size.unwrap(),
        );
        assert(log_metadata_table.valid());

        let sm = MultilogStaticMetadata {
            id: multilog_id,
            num_logs: num_logs as u64,
            mask_cdb_addr: static_metadata_crc_end.unwrap(),
            mask0_addr: mask_cdb_end.unwrap(),
            mask0_crc_addr: mask0_end.unwrap(),
            mask1_addr: mask0_crc_end.unwrap(),
            mask1_crc_addr: mask1_end.unwrap(),
            log_metadata_table,
            log_metadata_row_constants_addr: 0,
            log_metadata_row_constants_crc_addr: log_metadata_row_constants_end.unwrap(),
            log_metadata_row_dynamic_metadata0_addr: log_metadata_row_constants_crc_end.unwrap(),
            log_metadata_row_dynamic_metadata0_crc_addr:
                log_metadata_row_dynamic_metadata0_end.unwrap(),
            log_metadata_row_dynamic_metadata1_addr:
                log_metadata_row_dynamic_metadata0_crc_end.unwrap(),
            log_metadata_row_dynamic_metadata1_crc_addr:
                log_metadata_row_dynamic_metadata1_end.unwrap(),
        };
        assert(validate_static_metadata(sm, vm));

        let ghost all_log_constants = Seq::<SingleLogConstants>::new(
            sm.num_logs as nat,
            |i: int|
                SingleLogConstants {
                    log_area_start: (sm.log_metadata_table.end + spec_sum_u64s(
                        capacities@.take(i),
                    )) as u64,
                    log_area_end: (sm.log_metadata_table.end + spec_sum_u64s(
                        capacities@.take(i + 1),
                    )) as u64,
                },
        );
        let ghost all_log_dynamic_metadata = Seq::<SingleLogDynamicMetadata>::new(
            sm.num_logs as nat,
            |i: int| SingleLogDynamicMetadata { length: 0, head: 0 },
        );
        let ghost c = MultilogConstants { id: sm.id, capacities: capacities@ };
        let ghost state = AtomicMultilogState::initialize(sm.num_logs as nat);
        let ghost rm = MultilogRecoveryMapping {
            vm,
            sm,
            mask_cdb: false,
            mask: 0u64,
            all_log_constants,
            all_log_dynamic_metadata,
            c,
            state,
        };

        assert forall|i: int| #![trigger rm.all_log_constants[i]] 0 <= i < sm.num_logs implies {
            &&& rm.all_log_constants[i].log_area_start == sm.log_metadata_table.end + spec_sum_u64s(
                capacities@.take(i),
            )
            &&& rm.all_log_constants[i].log_area_end == sm.log_metadata_table.end + spec_sum_u64s(
                capacities@.take(i + 1),
            )
        } by {
            lemma_sum_u64s_bound(capacities@, i);
            lemma_sum_u64s_bound(capacities@, i + 1);
        }
        assert forall|i: int, j: int|
            0 <= i && i < j < rm.sm.num_logs implies #[trigger] rm.all_log_constants[i].log_area_end
            <= #[trigger] rm.all_log_constants[j].log_area_start by {
            lemma_sum_u64s_increases(capacities@, i + 1, j);
        }
        assert forall|i: int|
            #![trigger rm.c.capacities[i]]
            #![trigger rm.all_log_constants[i]]
            0 <= i < sm.num_logs implies {
            &&& rm.c.capacities[i] == rm.all_log_constants[i].log_area_end
                - rm.all_log_constants[i].log_area_start
            &&& rm.c.capacities[i] > 0
        } by {
            lemma_sum_u64s_step(capacities@, i);
        }

        assert(rm.state_corresponds_to_dynamic_metadata());
        Self::setup_given_metadata(pm_region, capacities, &vm, &sm, Ghost(rm))
    }
}

} // verus!
