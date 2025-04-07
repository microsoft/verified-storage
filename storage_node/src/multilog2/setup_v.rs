#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::invariant;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use super::impl_v::UntrustedMultilogImpl;
use super::recover_v::*;
use super::spec_t::*;
use vstd::arithmetic::overflow::CheckedU64;

verus! {

pub open(super) spec fn spec_sum_u64s(s: Seq<u64>) -> nat
{
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

impl UntrustedMultilogImpl
{
    pub open(super) spec fn spec_space_needed_for_setup(capacities: Seq<u64>) -> nat
    {
        // First calculate the size of the log metadata table.        
        let log_metadata_row_constants_end = SingleLogConstants::spec_size_of();
        let log_metadata_row_constants_crc_end = log_metadata_row_constants_end + u64::spec_size_of();
        let log_metadata_row_dynamic_metadata0_end = log_metadata_row_constants_crc_end + SingleLogDynamicMetadata::spec_size_of();
        let log_metadata_row_dynamic_metadata0_crc_end = log_metadata_row_dynamic_metadata0_end + u64::spec_size_of();
        let log_metadata_row_dynamic_metadata1_end = log_metadata_row_dynamic_metadata0_crc_end + SingleLogDynamicMetadata::spec_size_of();
        let log_metadata_row_dynamic_metadata1_crc_end = log_metadata_row_dynamic_metadata1_end + u64::spec_size_of();
        let log_metatata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metatata_table_row_size * capacities.len();

        // Next calculate the size needed for the log data.
        let total_capacity: nat = spec_sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = MultilogVersionMetadata::spec_size_of();
        let version_metadata_crc_end = version_metadata_end + u64::spec_size_of();
        let static_metadata_end = version_metadata_crc_end + MultilogStaticMetadata::spec_size_of();
        let static_metadata_crc_end = static_metadata_end + u64::spec_size_of();
        let mask_cdb_start = round_up_to_alignment(static_metadata_crc_end as int, u64::spec_align_of() as int) as nat;
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
                Err(MultilogErr::SpaceNeededForSetupExceedsMax) =>
                    Self::spec_space_needed_for_setup(capacities@) > u64::MAX,
                Err(_) => false,
            },
    {
        // First calculate the size of the log metadata table.        
        let log_metadata_row_constants_end = CheckedU64::new(size_of::<SingleLogConstants>() as u64);
        let log_metadata_row_constants_crc_end =
            log_metadata_row_constants_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata0_end =
            log_metadata_row_constants_crc_end.add_value(size_of::<SingleLogDynamicMetadata>() as u64);
        let log_metadata_row_dynamic_metadata0_crc_end =
            log_metadata_row_dynamic_metadata0_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata1_end =
            log_metadata_row_dynamic_metadata0_crc_end.add_value(size_of::<SingleLogDynamicMetadata>() as u64);
        let log_metadata_row_dynamic_metadata1_crc_end =
            log_metadata_row_dynamic_metadata1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metadata_table_row_size.mul_value(capacities.len() as u64);

        // Next calculate the size needed for the log data.
        let total_capacity = sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = CheckedU64::new(size_of::<MultilogVersionMetadata>() as u64);
        let version_metadata_crc_end = version_metadata_end.add_value(size_of::<u64>() as u64);
        let static_metadata_end = version_metadata_crc_end.add_value(size_of::<MultilogStaticMetadata>() as u64);
        let static_metadata_crc_end = static_metadata_end.add_value(size_of::<u64>() as u64);
        let mask_cdb_start = align_checked_u64_to_usize(&static_metadata_crc_end, align_of::<u64>());
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
        }
        else {
            Ok(log_areas_end.unwrap())
        }
    }

    exec fn setup_given_metadata<PMRegion>(
        pm_region: &mut PMRegion,
        capacities: &Vec<u64>,
        vm: &MultilogVersionMetadata,
        sm: &MultilogStaticMetadata,
    ) -> (result: Result<(), MultilogErr>)
        where
            PMRegion: PersistentMemoryRegion
        requires
            old(pm_region).inv(),
            old(pm_region)@.valid(),
            old(pm_region)@.len() >= sm.log_metadata_table.end + spec_sum_u64s(capacities@),
            old(pm_region)@.len() >= MultilogVersionMetadata::spec_size_of() + u64::spec_size_of(),
            old(pm_region)@.len() >= vm.static_metadata_addr + MultilogStaticMetadata::spec_size_of() + u64::spec_size_of(),
            old(pm_region)@.len() <= u64::MAX,
            validate_version_metadata(*vm),
            validate_static_metadata(*sm),
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
                _ => false
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
        pm_region.serialize_and_write::<u64>(vm.static_metadata_addr + size_of::<MultilogStaticMetadata>() as u64, &sm_crc);
        assert(recover_static_metadata(pm_region@.read_state, *vm) == Some(*sm));

        assume(false);
        Err(MultilogErr::NotYetImplemented)
    }
    
    // The `setup` method sets up persistent memory objects `pm_region`
    // to store an initial empty log. It returns the capacity of the log.
    // See `README.md` for more documentation.
    pub exec fn setup<PMRegion>(
        pm_region: &mut PMRegion,
        multilog_id: u128,
        capacities: &Vec<u64>,
    ) -> (result: Result<(), MultilogErr>)
        where
            PMRegion: PersistentMemoryRegion
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
                Err(MultilogErr::CantSetupWithMoreThanMaxRegions{ max_num_regions }) => {
                    &&& pm_region@ == old(pm_region)@
                    &&& capacities@.len() > max_num_regions
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
                _ => false
            }
    {
        let num_logs = capacities.len();
        if num_logs == 0 {
            return Err(MultilogErr::CantSetupWithFewerThanOneRegion);
        }
        if num_logs > MAX_NUM_LOGS {
            return Err(MultilogErr::CantSetupWithMoreThanMaxRegions { max_num_regions: MAX_NUM_LOGS });
        }

        // First calculate the size of the log metadata table.        
        let log_metadata_row_constants_end = CheckedU64::new(size_of::<SingleLogConstants>() as u64);
        let log_metadata_row_constants_crc_end =
            log_metadata_row_constants_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata0_end =
            log_metadata_row_constants_crc_end.add_value(size_of::<SingleLogDynamicMetadata>() as u64);
        let log_metadata_row_dynamic_metadata0_crc_end =
            log_metadata_row_dynamic_metadata0_end.add_value(size_of::<u64>() as u64);
        let log_metadata_row_dynamic_metadata1_end =
            log_metadata_row_dynamic_metadata0_crc_end.add_value(size_of::<SingleLogDynamicMetadata>() as u64);
        let log_metadata_row_dynamic_metadata1_crc_end =
            log_metadata_row_dynamic_metadata1_end.add_value(size_of::<u64>() as u64);
        let log_metadata_table_row_size = log_metadata_row_dynamic_metadata1_crc_end;
        let log_metadata_table_size = log_metadata_table_row_size.mul_value(capacities.len() as u64);
        assert(log_metadata_table_size@ == capacities@.len() * log_metadata_table_row_size@) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(capacities@.len() as int, log_metadata_table_row_size@ as int);
        }
        assert(log_metadata_table_size@ >= log_metadata_table_row_size@) by {
            vstd::arithmetic::mul::lemma_mul_ordering(capacities@.len() as int, log_metadata_table_row_size@ as int);
        }

        // Next calculate the size needed for the log data.
        let total_capacity = sum_u64s(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = CheckedU64::new(size_of::<MultilogVersionMetadata>() as u64);
        let version_metadata_crc_end = version_metadata_end.add_value(size_of::<u64>() as u64);
        let static_metadata_end = version_metadata_crc_end.add_value(size_of::<MultilogStaticMetadata>() as u64);
        let static_metadata_crc_end = static_metadata_end.add_value(size_of::<u64>() as u64);
        let mask_cdb_start = align_checked_u64_to_usize(&static_metadata_crc_end, align_of::<u64>());
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

        let vm = MultilogVersionMetadata{
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
            num_logs: num_logs as u32,
            mask_cdb_addr: static_metadata_crc_end.unwrap(),
            mask0_addr: mask_cdb_end.unwrap(),
            mask0_crc_addr: mask0_end.unwrap(),
            mask1_addr: mask0_crc_end.unwrap(),
            mask1_crc_addr: mask1_end.unwrap(),
            log_metadata_table,
            log_metadata_row_constants_addr: 0,
            log_metadata_row_constants_crc_addr: log_metadata_row_constants_end.unwrap(),
            log_metadata_row_dynamic_metadata0_addr: log_metadata_row_constants_crc_end.unwrap(),
            log_metadata_row_dynamic_metadata0_crc_addr: log_metadata_row_dynamic_metadata0_end.unwrap(),
            log_metadata_row_dynamic_metadata1_addr: log_metadata_row_dynamic_metadata0_crc_end.unwrap(),
            log_metadata_row_dynamic_metadata1_crc_addr: log_metadata_row_dynamic_metadata1_end.unwrap(),
        };
        assert(validate_static_metadata(sm));

        Self::setup_given_metadata(pm_region, capacities, &vm, &sm)
    }

}

}
