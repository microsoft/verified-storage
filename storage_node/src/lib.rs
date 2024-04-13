#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

pub mod multilog;
pub mod pmem;

use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::pmem::device_t::*;
// use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::timestamp_t::*;

// mod tests {
//     use super::*;
//     /// This test ensures that the hardcoded constant size of each metadata structure
//     /// matches the actual size at runtime. This helps ensure that the serde specification
//     /// for each structure is correct.
//     // #[verifier::external_body]
//     #[test]
//     fn check_layout() {
//         let global_metadata_size =
//             core::mem::size_of::<crate::multilog::layout_v::GlobalMetadata>();
//         let region_metadata_size =
//             core::mem::size_of::<crate::multilog::layout_v::RegionMetadata>();
//         let log_metadata_size = core::mem::size_of::<crate::multilog::layout_v::LogMetadata>();

//         println!("global metadata struct size: {:?}\n", global_metadata_size);
//         println!("region metadata struct size: {:?}\n", region_metadata_size);
//         println!("log metadata struct size: {:?}\n", log_metadata_size);

//         assert!(global_metadata_size == LENGTH_OF_GLOBAL_METADATA.try_into().unwrap());
//         assert!(region_metadata_size == LENGTH_OF_REGION_METADATA.try_into().unwrap());
//         assert!(log_metadata_size == LENGTH_OF_LOG_METADATA.try_into().unwrap());
//     }

//     // #[verifier::external_body]
//     // #[test]
//     // fn check_multilog_with_timestamps() {
//     //     assert(test_multilog_with_timestamps());
//     // }
// }

verus! {
    #[allow(dead_code)]
    fn main() {}


    // // this function is defined outside of the test module so that we can both
    // // run verification on it and call it in a test to ensure that all operations
    // // succeed
    // #[allow(dead_code, unused_variables, unused_mut)]
    // fn test_multilog_with_timestamps() -> bool {
    //     // TODO: ideally we wouldn't invoke this from trusted code, but we need it to prove the relationships
    //     // between different timestamps from the same region
    //     proof { lemma_auto_timestamp_helpers(); }

    //     // set up vectors to mock persistent memory
    //     let device_capacity = 1024;
    //     let log_capacity = 256;
    //     // obtain a device abstraction with enough space for the requested regions
    //     let mut device = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);

    //     // multilog1 regions
    //     let region1_desc = device.get_new_region(log_capacity).unwrap();
    //     let region2_desc = device.get_new_region(log_capacity).unwrap();
    //     let region1 = VolatileMemoryMockingPersistentMemoryRegion::new(region1_desc).unwrap();
    //     let region2 = VolatileMemoryMockingPersistentMemoryRegion::new(region2_desc).unwrap();


    //     // multilog2 regions
    //     let region3_desc = device.get_new_region(log_capacity).unwrap();
    //     let region4_desc = device.get_new_region(log_capacity).unwrap();
    //     let region3 = VolatileMemoryMockingPersistentMemoryRegion::new(region3_desc).unwrap();
    //     let region4 = VolatileMemoryMockingPersistentMemoryRegion::new(region4_desc).unwrap();

    //     let mut log1_vec = Vec::new();
    //     log1_vec.push(region1); log1_vec.push(region2);
    //     let mut log2_vec = Vec::new();
    //     log2_vec.push(region3); log2_vec.push(region4);

    //     // combine individual regions into groups so we can use them to set up multilogs
    //     let mut multilog1_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log1_vec);
    //     let mut multilog2_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log2_vec);

    //     let result = MultiLogImpl::setup(&mut multilog1_regions);
    //     let (_log1_capacities, multilog_id1) = match result {
    //         Ok((log1_capacities, multilog_id)) => (log1_capacities, multilog_id),
    //         Err(_) => return false
    //     };

    //     let result = MultiLogImpl::setup(&mut multilog2_regions);
    //     let (_log2_capacities, multilog_id2) = match result {
    //         Ok((log2_capacities, multilog_id)) => (log2_capacities, multilog_id),
    //         Err(_) => return false
    //     };

    //     // set up a second device
    //     let mut device2 = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);
    //     let region5_desc = device2.get_new_region(log_capacity).unwrap();
    //     let region6_desc = device2.get_new_region(log_capacity).unwrap();
    //     let region5 = VolatileMemoryMockingPersistentMemoryRegion::new(region5_desc).unwrap();
    //     let region6 = VolatileMemoryMockingPersistentMemoryRegion::new(region6_desc).unwrap();

    //     let mut log3_vec = Vec::new();
    //     log3_vec.push(region5); log3_vec.push(region6);

    //     let mut multilog3_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log3_vec);

    //     let result = MultiLogImpl::setup(&mut multilog3_regions);
    //     let (_log3_capacities, multilog_id3) = match result {
    //         Ok((log3_capacities, multilog_id)) => (log3_capacities, multilog_id),
    //         Err(_) => return false
    //     };

    //     // start the logs
    //     let result = MultiLogImpl::start(multilog1_regions, multilog_id1);
    //     let mut multilog1 = match result {
    //         Ok(multilog) => multilog,
    //         Err(_) => return false
    //     };

    //     let result = MultiLogImpl::start(multilog2_regions, multilog_id2);
    //     let mut multilog2 = match result {
    //         Ok(multilog) => multilog,
    //         Err(_) => return false
    //     };

    //     let result = MultiLogImpl::start(multilog3_regions, multilog_id3);
    //     let mut multilog3 = match result {
    //         Ok(multilog) => multilog,
    //         Err(_) => return false
    //     };

    //     let mut vec = Vec::new();
    //     vec.push(1); vec.push(2); vec.push(3);

    //     let ghost old1 = multilog1;
    //     let ghost old2 = multilog2;

    //     let result1 = multilog1.tentatively_append(0, vec.as_slice());
    //     let result2 = multilog1.tentatively_append(1, vec.as_slice());
    //     match (result1, result2) {
    //         (Ok(_), Ok(_)) => {}
    //         _=> return false
    //     }

    //     let result1 = multilog2.tentatively_append(0, vec.as_slice());
    //     let result2 = multilog2.tentatively_append(1, vec.as_slice());
    //     match (result1, result2) {
    //         (Ok(_), Ok(_)) => {}
    //         _=> return false
    //     }

    //     let result = multilog2.commit();
    //     match result {
    //         Ok(_) => {}
    //         _ => return false
    //     }

    //     // we should now be able to (attempt) to update multilog1's ghost state using multilog2's
    //     // timestamp. doing so here is kind of silly (we can't do anything differently); it's just
    //     // to make sure the interface works and makes some sense.

    //     // I should be allowed to (as in, verification will succeed) try to update
    //     // multilog1's timestamp using multilog2's.
    //     multilog1.update_timestamp(Ghost(multilog2.get_timestamp()));

    //     // // this should not verify, because multilog3 is on a different device from
    //     // // multilog2
    //     // multilog3.update_timestamp(Ghost(multilog2.get_timestamp()));

    //     let result = multilog1.commit();
    //     match result {
    //         Ok(_) => {}
    //         _ => return false
    //     }

    //     let result = multilog2.advance_head(0, 2);
    //     match result {
    //         Ok(_) => {}
    //         _ => return false
    //     }

    //     let result = multilog1.advance_head(0, 2);
    //     match result {
    //         Ok(_) => {}
    //         _ => return false
    //     }

    //     // multilog1's timestamp is now ahead of multilog2's, so we can update
    //     // multilog2
    //     multilog2.update_timestamp(Ghost(multilog1.get_timestamp()));

    //     // Note: The timestamp function can only be called with a timestamp
    //     // that is provably greater than the timestamp of the component
    //     // we are trying to update. We could write it as a no-op when the
    //     // given timestamp is lte the component, but that just kicks the can
    //     // down the road to the next time you want prove something about what
    //     // is and is not persistent.

    //     true
    // }
}
