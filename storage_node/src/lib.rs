#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

pub mod kv;
pub mod multilog;
pub mod pmem;

use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::multilog::multilogspec_t::*;
use crate::pmem::device_t::*;
#[cfg(target_os = "linux")]
use crate::pmem::linux_pmemfile_t::*;
#[cfg(target_os = "windows")]
use crate::pmem::windows_pmemfile_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::timestamp_t::*;

mod tests {
    use super::*;
    /// This test ensures that the hardcoded constant size of each metadata structure
    /// matches the actual size at runtime. This helps ensure that the serde specification
    /// for each structure is correct.
    // #[verifier::external_body]
    #[test]
    fn check_layout() {
        let global_metadata_size =
            core::mem::size_of::<crate::multilog::layout_v::GlobalMetadata>();
        let region_metadata_size =
            core::mem::size_of::<crate::multilog::layout_v::RegionMetadata>();
        let log_metadata_size = core::mem::size_of::<crate::multilog::layout_v::LogMetadata>();

        println!("global metadata struct size: {:?}\n", global_metadata_size);
        println!("region metadata struct size: {:?}\n", region_metadata_size);
        println!("log metadata struct size: {:?}\n", log_metadata_size);

        assert!(global_metadata_size == LENGTH_OF_GLOBAL_METADATA.try_into().unwrap());
        assert!(region_metadata_size == LENGTH_OF_REGION_METADATA.try_into().unwrap());
        assert!(log_metadata_size == LENGTH_OF_LOG_METADATA.try_into().unwrap());
    }

    #[test]
    fn check_multilog_with_timestamps() {
        assert!(test_multilog_with_timestamps());
    }
}

verus! {
    // this function is defined outside of the test module so that we can both
    // run verification on it and call it in a test to ensure that all operations
    // succeed
    #[allow(dead_code, unused_variables, unused_mut)]
    fn test_multilog_with_timestamps() -> bool {
        // TODO: ideally we wouldn't invoke this from trusted code, but we need it to prove the relationships
        // between different timestamps from the same region
        proof { lemma_auto_timestamp_helpers(); }

        // set up vectors to mock persistent memory
        let device_capacity = 4096;
        let log_capacity = 512;
        // obtain a device abstraction with enough space for the requested regions
        let mut device = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);

        // multilog1 regions
        let region1_desc = device.get_new_region(log_capacity).unwrap();
        let region2_desc = device.get_new_region(log_capacity).unwrap();
        let region1 = VolatileMemoryMockingPersistentMemoryRegion::new(region1_desc).unwrap();
        let region2 = VolatileMemoryMockingPersistentMemoryRegion::new(region2_desc).unwrap();


        // multilog2 regions
        let region3_desc = device.get_new_region(log_capacity).unwrap();
        let region4_desc = device.get_new_region(log_capacity).unwrap();
        let region3 = VolatileMemoryMockingPersistentMemoryRegion::new(region3_desc).unwrap();
        let region4 = VolatileMemoryMockingPersistentMemoryRegion::new(region4_desc).unwrap();

        let mut log1_vec = Vec::new();
        log1_vec.push(region1); log1_vec.push(region2);
        let mut log2_vec = Vec::new();
        log2_vec.push(region3); log2_vec.push(region4);

        // combine individual regions into groups so we can use them to set up multilogs
        let mut multilog1_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log1_vec);
        let mut multilog2_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log2_vec);

        let result = MultiLogImpl::setup(&mut multilog1_regions);
        let (_log1_capacities, multilog_id1) = match result {
            Ok((log1_capacities, multilog_id)) => (log1_capacities, multilog_id),
            Err(_) => return false
        };

        let result = MultiLogImpl::setup(&mut multilog2_regions);
        let (_log2_capacities, multilog_id2) = match result {
            Ok((log2_capacities, multilog_id)) => (log2_capacities, multilog_id),
            Err(_) => return false
        };

        // set up a second device
        let mut device2 = VolatileMemoryMockingPersistentMemoryDevice::new(device_capacity);
        let region5_desc = device2.get_new_region(log_capacity).unwrap();
        let region6_desc = device2.get_new_region(log_capacity).unwrap();
        let region5 = VolatileMemoryMockingPersistentMemoryRegion::new(region5_desc).unwrap();
        let region6 = VolatileMemoryMockingPersistentMemoryRegion::new(region6_desc).unwrap();

        let mut log3_vec = Vec::new();
        log3_vec.push(region5); log3_vec.push(region6);

        let mut multilog3_regions = VolatileMemoryMockingPersistentMemoryRegions::combine_regions(log3_vec);

        let result = MultiLogImpl::setup(&mut multilog3_regions);
        let (_log3_capacities, multilog_id3) = match result {
            Ok((log3_capacities, multilog_id)) => (log3_capacities, multilog_id),
            Err(_) => return false
        };

        // start the logs
        let result = MultiLogImpl::start(multilog1_regions, multilog_id1);
        let mut multilog1 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let result = MultiLogImpl::start(multilog2_regions, multilog_id2);
        let mut multilog2 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let result = MultiLogImpl::start(multilog3_regions, multilog_id3);
        let mut multilog3 = match result {
            Ok(multilog) => multilog,
            Err(_) => return false
        };

        let mut vec = Vec::new();
        vec.push(1); vec.push(2); vec.push(3);

        let ghost old1 = multilog1;
        let ghost old2 = multilog2;

        let result1 = multilog1.tentatively_append(0, vec.as_slice());
        let result2 = multilog1.tentatively_append(1, vec.as_slice());
        match (result1, result2) {
            (Ok(_), Ok(_)) => {}
            _=> return false
        }

        let result1 = multilog2.tentatively_append(0, vec.as_slice());
        let result2 = multilog2.tentatively_append(1, vec.as_slice());
        match (result1, result2) {
            (Ok(_), Ok(_)) => {}
            _=> return false
        }

        let result = multilog2.commit();
        match result {
            Ok(_) => {}
            _ => return false
        }

        // we should now be able to (attempt) to update multilog1's ghost state using multilog2's
        // timestamp. doing so here is kind of silly (we can't do anything differently); it's just
        // to make sure the interface works and makes some sense.

        // I should be allowed to (as in, verification will succeed) try to update
        // multilog1's timestamp using multilog2's.
        multilog1.update_timestamp(Ghost(multilog2.get_timestamp()));

        // // this should not verify, because multilog3 is on a different device from
        // // multilog2
        // multilog3.update_timestamp(Ghost(multilog2.get_timestamp()));

        let result = multilog1.commit();
        match result {
            Ok(_) => {}
            _ => return false
        }

        let result = multilog2.advance_head(0, 2);
        match result {
            Ok(_) => {}
            _ => return false
        }

        let result = multilog1.advance_head(0, 2);
        match result {
            Ok(_) => {}
            _ => return false
        }

        // multilog1's timestamp is now ahead of multilog2's, so we can update
        // multilog2
        multilog2.update_timestamp(Ghost(multilog1.get_timestamp()));

        // Note: The timestamp function can only be called with a timestamp
        // that is provably greater than the timestamp of the component
        // we are trying to update. We could write it as a no-op when the
        // given timestamp is lte the component, but that just kicks the can
        // down the road to the next time you want prove something about what
        // is and is not persistent.

        true
    }

    #[cfg(target_os = "windows")]
    fn windows_create_multilog() -> (multilog: Option<MultiLogImpl<FileBackedPersistentMemoryRegions>>)
        ensures
            match multilog {
                Some(multilog) => {
                    &&& multilog@.num_logs() == 2
                    &&& multilog@[0] == AbstractLogState::initialize(multilog@[0].capacity)
                    &&& multilog@[1] == AbstractLogState::initialize(multilog@[1].capacity)
                    &&& multilog.valid()
                },
                None => true,
            }
    {
        // To test the multilog, we use files in the current directory that mock persistent-memory
        // regions. Here we use such regions, one of size 4096 and one of size 1024.
        let mut region_sizes: Vec<u64> = Vec::<u64>::new();
        region_sizes.push(4096);
        region_sizes.push(1024);

        // Create the multipersistent memory out of the two regions.
        let file_name = vstd::string::new_strlit("test_multilog");
        let mut pm_regions = FileBackedPersistentMemoryRegions::new(&file_name, MemoryMappedFileMediaType::SSD,
                                                                    region_sizes.as_slice(),
                                                                    FileCloseBehavior::TestingSoDeleteOnClose).ok()?;

        // Set up the memory regions to contain a multilog. The capacities will be less
        // than 4096 and 1024 because a few bytes are needed in each region for metadata.
        let (capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions).ok()?;
        runtime_assert(capacities.len() == 2);
        runtime_assert(capacities[0] <= 4096);
        runtime_assert(capacities[1] <= 1024);

        // Start accessing the multilog.
        MultiLogImpl::start(pm_regions, multilog_id).ok()
    }

    #[cfg(target_os = "linux")]
    fn linux_create_multilog() -> (multilog: Option<MultiLogImpl<MappedPmRegions>>)
        ensures
            match multilog {
                Some(multilog) => {
                    &&& multilog@.num_logs() == 2
                    &&& multilog@[0] == AbstractLogState::initialize(multilog@[0].capacity)
                    &&& multilog@[1] == AbstractLogState::initialize(multilog@[1].capacity)
                    &&& multilog.valid()
                },
                None => true,
            }
    {
        // To test the multilog, we use files in the current directory that mock persistent-memory
        // regions. Here we use such regions, one of size 4096 and one of size 1024.
        let mut region_sizes: Vec<u64> = Vec::<u64>::new();
        region_sizes.push(4096);
        region_sizes.push(1024);

        // Create the multipersistent memory out of the two regions.
        let file_name = vstd::string::new_strlit("test_multilog");
        let mut pm_dev = crate::pmem::linux_pmemfile_t::MappedPmDevice::new_testing_only(
            file_name,
            (region_sizes[0] + region_sizes[1]) as usize,
        ).ok()?;
        let mut regions = Vec::<MappedPM>::new();
        let region_desc0 = pm_dev.get_new_region(region_sizes[0]).ok()?;
        let region0 = MappedPM::new(region_desc0).ok()?;
        regions.push(region0);
        let region_desc1 = pm_dev.get_new_region(region_sizes[1]).ok()?;
        let region1 = MappedPM::new(region_desc1).ok()?;
        regions.push(region1);
        let mut pm_regions = crate::pmem::linux_pmemfile_t::MappedPmRegions::combine_regions(regions);
        assert(pm_regions@[0].len() == 4096);
        assert(pm_regions@[1].len() == 1024);

        // Set up the memory regions to contain a multilog. The capacities will be less
        // than 4096 and 1024 because a few bytes are needed in each region for metadata.
        let (capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions).ok()?;
        runtime_assert(capacities.len() == 2);
        runtime_assert(capacities[0] <= 4096);
        runtime_assert(capacities[1] <= 1024);

        // Start accessing the multilog.
        MultiLogImpl::start(pm_regions, multilog_id).ok()
    }

    fn test_multilog_on_memory_mapped_file() -> Option<()>
    {
        #[cfg(target_os = "windows")]
        let mut multilog = windows_create_multilog()?;
        #[cfg(target_os = "linux")]
        let mut multilog = linux_create_multilog()?;

        // Tentatively append [30, 42, 100] to log #0 of the multilog.
        let mut v: Vec<u8> = Vec::<u8>::new();
        v.push(30); v.push(42); v.push(100);
        let pos = multilog.tentatively_append(0, v.as_slice()).ok()?;
        runtime_assert(pos == 0);

        // Note that a tentative append doesn't actually advance the tail. That
        // doesn't happen until the next commit.
        let (head, tail, _capacity) = multilog.get_head_tail_and_capacity(0).ok()?;
        runtime_assert(head == 0);
        runtime_assert(tail == 0);

        // Also tentatively append [30, 42, 100, 152] to log #1. This still doesn't
        // commit anything to the log.
        v.push(152);
        let pos = multilog.tentatively_append(1, v.as_slice()).ok()?;
        runtime_assert(pos == 0);

        // Now commit the tentative appends. This causes log #0 to have tail 3
        // and log #1 to have tail 4.
        if multilog.commit().is_err() {
            runtime_assert(false); // can't fail
        }
        match multilog.get_head_tail_and_capacity(0) {
            Ok((head, tail, capacity)) => {
                runtime_assert(head == 0);
                runtime_assert(tail == 3);
            },
            _ => runtime_assert(false) // can't fail
        }
        match multilog.get_head_tail_and_capacity(1) {
            Ok((head, tail, capacity)) => {
                runtime_assert(head == 0);
                runtime_assert(tail == 4);
            },
            _ => runtime_assert(false) // can't fail
        }

        // We read the 2 bytes starting at position 1 of log #0. We should
        // read bytes [42, 100]. This is only guaranteed if the memory
        // wasn't corrupted.
        if let Ok(bytes) = multilog.read(0, 1, 2) {
            runtime_assert(bytes.len() == 2);
            assert(multilog.constants().impervious_to_corruption ==> bytes[0] == 42);
        }

        // We now advance the head of log #0 to position 2. This causes the
        // head to become 2 and the tail stays at 3.
        match multilog.advance_head(0, 2) {
            Ok(()) => runtime_assert(true),
            _ => runtime_assert(false) // can't fail
        }
        match multilog.get_head_tail_and_capacity(0) {
            Ok((head, tail, capacity)) => {
                runtime_assert(head == 2);
                runtime_assert(tail == 3);
            },
            _ => runtime_assert(false) // can't fail
        }

        // If we read from position 2 of log #0, we get the same thing we
        // would have gotten before the advance-head operation.
        if let Ok(bytes) = multilog.read(0, 2, 1) {
            assert(multilog.constants().impervious_to_corruption ==> bytes[0] == 100);
        }

        // But if we try to read from position 0 of log #0, we get an
        // error because we're not allowed to read from before the head.
        match multilog.read(0, 0, 1) {
            Err(MultiLogErr::CantReadBeforeHead{head}) => runtime_assert(head == 2),
            _ => runtime_assert(false) // can't succeed, and can't fail with any other error
        }
        Some(())
    }

    #[allow(dead_code)]
    fn main()
    {
        test_multilog_with_timestamps();
        test_multilog_on_memory_mapped_file();
    }
}
