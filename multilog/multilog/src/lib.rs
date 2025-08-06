#![feature(maybe_uninit_as_bytes)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_write_slice)]
#![allow(unused_imports)]

use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

pub mod multilog;
pub mod pmem;

use crate::multilog::layout_v::*;
use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::multilog::multilogspec_t::*;
#[cfg(all(target_os = "linux", feature = "pmem"))]
use crate::pmem::linux_pmemfile_t::*;
#[cfg(target_os = "windows")]
use crate::pmem::windows_pmemfile_t::*;
#[cfg(target_family = "unix")]
use crate::pmem::mmap_pmemfile_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;

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
fn check_multilog_in_volatile_memory() {
    assert!(test_multilog_in_volatile_memory());
}
    
}

verus! {
// this function is defined outside of the test module so that we can both
// run verification on it and call it in a test to ensure that all operations
// succeed
#[allow(dead_code, unused_variables, unused_mut)]
fn test_multilog_in_volatile_memory() -> bool {
    // set up vectors to mock persistent memory
    let mut region_sizes = Vec::<u64>::new();
    region_sizes.push(512);
    region_sizes.push(512);
    let mut regions = VolatileMemoryMockingPersistentMemoryRegions::new(region_sizes.as_slice());

    let result = MultiLogImpl::setup(&mut regions);
    let (_log_capacities, multilog_id) = match result {
        Ok((log_capacities, multilog_id)) => (log_capacities, multilog_id),
        Err(_) => return false,
    };

    // start the log
    let result = MultiLogImpl::start(regions, multilog_id);
    let mut multilog = match result {
        Ok(multilog) => multilog,
        Err(_) => return false,
    };

    let mut vec = Vec::new();
    vec.push(1); vec.push(2); vec.push(3);

    let result1 = multilog.tentatively_append(0, vec.as_slice());
    let result2 = multilog.tentatively_append(1, vec.as_slice());
    match (result1, result2) {
        (Ok(_), Ok(_)) => {},
        _=> return false,
    }

    let result = multilog.commit();
    match result {
        Ok(_) => {},
        _ => return false,
    }

    let result = multilog.advance_head(0, 2);
    match result {
        Ok(_) => {}
        _ => return false
    }

    true
}

fn test_multilog_on_memory_mapped_file() -> Option<()>
{
    // To test the multilog, we use files in the current directory that mock persistent-memory
    // regions. Here we use such regions, one of size 4096 and one of size 1024.
    let mut region_sizes: Vec<u64> = Vec::<u64>::new();
    region_sizes.push(4096);
    region_sizes.push(1024);

    // Create the multipersistent memory out of the two regions.
    let file_name = "test_multilog";
    #[cfg(target_os = "windows")]
    let mut pm_regions = FileBackedPersistentMemoryRegions::new(
        &file_name,
        MemoryMappedFileMediaType::SSD,
        region_sizes.as_slice(),
        FileCloseBehavior::TestingSoDeleteOnClose
    ).ok()?;
    #[cfg(all(target_os = "linux", feature = "pmem"))]
    let mut pm_regions = FileBackedPersistentMemoryRegions::new(
        &file_name,
        region_sizes.as_slice(),
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    ).ok()?;
    #[cfg(any(target_os = "macos", not(feature = "pmem")))]
    let mut pm_regions = FileBackedPersistentMemoryRegions::new(
        &file_name,
        region_sizes.as_slice(),
    ).ok()?;

    // Set up the memory regions to contain a multilog. The capacities will be less
    // than 4096 and 1024 because a few bytes are needed in each region for metadata.
    let (capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions).ok()?;
    runtime_assert(capacities.len() == 2);
    runtime_assert(capacities[0] <= 4096);
    runtime_assert(capacities[1] <= 1024);

    // Start accessing the multilog.
    let mut multilog = MultiLogImpl::start(pm_regions, multilog_id).ok()?;

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
        Ok((head, tail, _capacity)) => {
            runtime_assert(head == 0);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }
    match multilog.get_head_tail_and_capacity(1) {
        Ok((head, tail, _capacity)) => {
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
        Ok((head, tail, _capacity)) => {
            runtime_assert(head == 2);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }

    // If we read from position 2 of log #0, we get the same thing we
    // would have gotten before the advance-head operation.
    if let Ok(_bytes) = multilog.read(0, 2, 1) {
        assert(multilog.constants().impervious_to_corruption ==> _bytes[0] == 100);
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
    test_multilog_in_volatile_memory();
    test_multilog_on_memory_mapped_file();
}
}
