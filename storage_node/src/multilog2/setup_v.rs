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
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use super::impl_v::UntrustedMultilogImpl;
use super::recover_v::MultilogStaticMetadata;
use super::recover_v::MultilogVersionMetadata;
use super::recover_v::SingleLogConstants;
use super::recover_v::SingleLogDynamicMetadata;
use super::spec_t::*;
use vstd::arithmetic::overflow::CheckedU64;

verus! {

exec fn sum_capacities(capacities: &Vec<u64>) -> (result: CheckedU64)
    ensures
        result@ == capacities@.fold_left(0nat, |acc: nat, x: u64| (acc + x) as nat),
{
    let mut result = CheckedU64::new(0u64);
    for n in 0..capacities.len()
        invariant
            result@ == capacities@.take(n as int).fold_left(0nat, |acc: nat, x: u64| (acc + x) as nat),
    {
        result = result.add_value(capacities[n]);
        assert(capacities@.take(n + 1).drop_last() =~= capacities@.take(n as int));
        assert(capacities@.take(n + 1).last() == capacities@[n as int]);
    }
    assert(capacities@.take(capacities.len() as int) == capacities@);
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
        let total_capacity: nat = capacities.fold_left(0nat, |acc: nat, x: u64| (acc + x) as nat);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = MultilogVersionMetadata::spec_size_of();
        let version_metadata_crc_end = version_metadata_end + u64::spec_size_of();
        let static_metadata_end = version_metadata_crc_end + MultilogStaticMetadata::spec_size_of();
        let static_metadata_crc_end = static_metadata_end + u64::spec_size_of();
        let mask_cdb_end = static_metadata_crc_end + u64::spec_size_of();
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
        let total_capacity = sum_capacities(capacities);

        // Then calculate the offsets of each piece of the storage.
        let version_metadata_end = CheckedU64::new(size_of::<MultilogVersionMetadata>() as u64);
        let version_metadata_crc_end = version_metadata_end.add_value(size_of::<u64>() as u64);
        let static_metadata_end = version_metadata_crc_end.add_value(size_of::<MultilogStaticMetadata>() as u64);
        let static_metadata_crc_end = static_metadata_end.add_value(size_of::<u64>() as u64);
        let mask_cdb_end = static_metadata_crc_end.add_value(size_of::<u64>() as u64);
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
}

}
