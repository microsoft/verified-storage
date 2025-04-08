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

proof fn lemma_sum_u64s_step(s: Seq<u64>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(s.take(i)) + s[i]
{
    assert(s.take(i + 1).drop_last() =~= s.take(i));
    assert(s.take(i + 1).last() == s[i]);
}

proof fn lemma_sum_u64s_increases(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s.take(j)),
    decreases
        j - i,
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
    decreases
        s.len() - i,
{
    if i < s.len() {
        lemma_sum_u64s_bound(s, i + 1);
        lemma_sum_u64s_step(s, i);
    }
    else {
        assert(s.take(i) =~= s);
    }
}

proof fn lemma_sum_u64s_forall(s: Seq<u64>)
    ensures
        forall|i: int| 0 <= i < s.len() ==> 
            spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(s.take(i)) + #[trigger] s[i],
        forall|i: int| 0 <= i <= s.len() ==>
            #[trigger] spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s),
{
    assert forall|i: int| 0 <= i < s.len() implies
            spec_sum_u64s(s.take(i + 1)) == spec_sum_u64s(s.take(i)) + #[trigger] s[i] by {
        lemma_sum_u64s_step(s, i);
    }
    assert forall|i: int| 0 <= i <= s.len() implies #[trigger] spec_sum_u64s(s.take(i)) <= spec_sum_u64s(s) by {
        lemma_sum_u64s_bound(s, i);
    }
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
            sm.num_logs == capacities.len(),
            forall|i: int| 0 <= i < capacities@.len() ==> #[trigger] capacities@[i] > 0,
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
        pm_region.serialize_and_write::<u64>(vm.static_metadata_addr + size_of::<MultilogStaticMetadata>() as u64,
                                             &sm_crc);
        assert(recover_static_metadata(pm_region@.read_state, *vm) == Some(*sm));

        let num_logs = capacities.len();
        let ghost mut cs: Seq<SingleLogConstants> = Seq::<SingleLogConstants>::empty();
        let mut current_offset = sm.log_metadata_table.end;
        assert(new_option_seq(0, |i: int| recover_single_log_constants(pm_region@.read_state, i, *sm)) =~=
               Some(Seq::<SingleLogConstants>::empty()));
        let d = SingleLogDynamicMetadata {
            length: 0,
            head: 0,
        };
        let d_crc = calculate_crc(&d);
        for which_log in 0..num_logs
            invariant
                pm_region.inv(),
                pm_region@.valid(),
                pm_region@.len() >= sm.log_metadata_table.end + spec_sum_u64s(capacities@),
                pm_region@.len() >= MultilogVersionMetadata::spec_size_of() + u64::spec_size_of(),
                pm_region@.len() >=
                    vm.static_metadata_addr + MultilogStaticMetadata::spec_size_of() + u64::spec_size_of(),
                pm_region@.len() <= u64::MAX,
                validate_version_metadata(*vm),
                validate_static_metadata(*sm),
                Some(cs) == new_option_seq(which_log as nat,
                                           |i: int| recover_single_log_constants(pm_region@.read_state, i, *sm)),
                0 < cs.len() ==> validate_all_log_constants(cs, *sm),
                current_offset == sm.log_metadata_table.end + spec_sum_u64s(capacities@.take(which_log as int)),
                forall|i: int| 0 <= i < cs.len() ==> #[trigger] cs[i].log_area_start ==
                                             sm.log_metadata_table.end + spec_sum_u64s(capacities@.take(i)),
                forall|i: int| 0 <= i < cs.len() ==> #[trigger] cs[i].log_area_end ==
                                             sm.log_metadata_table.end + spec_sum_u64s(capacities@.take(i + 1)),
                num_logs == capacities.len() == sm.num_logs,
                d == (SingleLogDynamicMetadata{ length: 0, head: 0 }),
                d_crc == spec_crc_u64(d.spec_to_bytes()),
                forall|i: int| 0 <= i < which_log ==>
                    recover_single_log_dynamic_metadata(pm_region@.read_state, i, *sm, 0) == Some(d),
                forall|i: int| 0 <= i < capacities@.len() ==> #[trigger] capacities@[i] > 0,
        {
            broadcast use group_update_bytes_effect;
            broadcast use group_validate_row_addr;
            broadcast use lemma_row_index_to_addr_is_valid;
            broadcast use pmcopy_axioms;

            let ghost old_pm_region = pm_region@.read_state;

            let row_addr = sm.log_metadata_table.row_index_to_addr(which_log as u64);
            assert(row_addr == sm.log_metadata_table.spec_row_index_to_addr(which_log as int));
            assert(spec_sum_u64s(capacities@.take(which_log + 1)) ==
                   spec_sum_u64s(capacities@.take(which_log as int)) + capacities[which_log as int]) by {
                lemma_sum_u64s_step(capacities@, which_log as int);
            }
            assert(spec_sum_u64s(capacities@.take(which_log + 1)) <= spec_sum_u64s(capacities@)) by {
                lemma_sum_u64s_bound(capacities@, which_log + 1);
            }
            let c = SingleLogConstants {
                log_area_start: current_offset,
                log_area_end: current_offset + capacities[which_log],
            };
            current_offset = current_offset + capacities[which_log];
            assert(current_offset == sm.log_metadata_table.end + spec_sum_u64s(capacities@.take(which_log + 1)));
            pm_region.serialize_and_write::<SingleLogConstants>(row_addr + sm.log_metadata_row_constants_addr, &c);
            let c_crc = calculate_crc(&c);
            pm_region.serialize_and_write::<u64>(row_addr + sm.log_metadata_row_constants_crc_addr, &c_crc);

            pm_region.serialize_and_write::<SingleLogDynamicMetadata>(row_addr + sm.log_metadata_row_dynamic_metadata0_addr, &d);
            pm_region.serialize_and_write::<u64>(row_addr + sm.log_metadata_row_dynamic_metadata0_crc_addr, &d_crc);

            assert(recover_single_log_constants(pm_region@.read_state, which_log as int, *sm) =~= Some(c));
            assert(recover_single_log_dynamic_metadata(pm_region@.read_state, which_log as int, *sm, 0) =~= Some(d));
            proof {
                cs = cs.push(c);
            }

            assert forall|i: int| 0 <= i <= which_log implies
                   #[trigger] recover_single_log_constants(pm_region@.read_state, i, *sm) == Some(cs[i]) by {
                if i < which_log {
                    assert(recover_single_log_constants(pm_region@.read_state, i, *sm) ==
                           recover_single_log_constants(old_pm_region, i, *sm));
                }
            }
            assert forall|i: int| 0 <= i <= which_log implies
                    #[trigger] recover_single_log_dynamic_metadata(pm_region@.read_state, i, *sm, 0) == Some(d) by {
                if i < which_log {
                    assert(recover_single_log_dynamic_metadata(pm_region@.read_state, i, *sm, 0) ==
                           recover_single_log_dynamic_metadata(old_pm_region, i, *sm, 0));
                }
            }
            assert(new_option_seq((which_log + 1) as nat,
                                  |i: int| recover_single_log_constants(pm_region@.read_state, i, *sm)) == Some(cs));
            assert(sm.log_metadata_table.end <= cs[0].log_area_start);
            assert forall|i: int, j: int| 0 <= i < j <= which_log implies
                    #[trigger] cs[i].log_area_end <= #[trigger] cs[j].log_area_start by {
                lemma_sum_u64s_increases(capacities@, i + 1, j);
            }
        }

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
                Err(MultilogErr::CapacityMustBePositive{ which_log }) => {
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

        for which_log in 0..num_logs
            invariant
                num_logs == capacities@.len(),
                forall|i: int| 0 <= i < which_log ==> capacities@[i] > 0,
                pm_region == old(pm_region),
                pm_region.inv(),
        {
            if capacities[which_log] == 0 {
                return Err(MultilogErr::CapacityMustBePositive{ which_log });
            }
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
