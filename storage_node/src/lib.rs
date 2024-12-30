#![feature(maybe_uninit_as_bytes)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_write_slice)]
#![feature(new_uninit)]

#![allow(unused_imports)]
#![allow(unused_braces)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(dead_code)]
#![allow(unused_mut)]
#![cfg(verus_keep_ghost)]

use builtin::*;
use builtin_macros::*;
//use kv::durable::list_v::*;
//use kv::durable::itemtable_v::*;
//use kv::durable::maintable_v::*;
use pmem::wrpm_t::*;
use vstd::pervasive::runtime_assert;
use vstd::prelude::*;

pub mod journal;
//pub mod kv;
pub mod kv2;
// pub mod log;
// pub mod multilog;
pub mod pmem;
pub mod common;
//pub mod log2;

//use kv::durable::durableimpl_v::*;
//use kv::kvspec_t::*;
//use kv::kvimpl_v::*;
//use kv::volatile::volatileimpl_v::*;
use crate::common::util_v::*;
// use crate::log::logimpl_t::*;
// use crate::multilog::layout_v::*;
// use crate::multilog::multilogimpl_t::*;
// use crate::multilog::multilogimpl_v::*;
// use crate::multilog::multilogspec_t::*;
//#[cfg(target_os = "linux")]
//use crate::pmem::linux_pmemfile_t::*;
//#[cfg(target_os = "windows")]
//use crate::pmem::windows_pmemfile_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;

mod tests {

use super::*;

// #[test]
// fn check_multilog_in_volatile_memory() {
//     assert!(test_multilog_in_volatile_memory());
// }

//#[test]
//fn check_durable_on_memory_mapped_file () {
//    test_durable_on_memory_mapped_file();
//}

//#[test]
//fn check_kv_on_memory_mapped_file () {
//    test_kv_on_memory_mapped_file();
//}
    
}

verus! {
// // this function is defined outside of the test module so that we can both
// // run verification on it and call it in a test to ensure that all operations
// // succeed
// #[allow(dead_code, unused_variables, unused_mut)]
// fn test_multilog_in_volatile_memory() -> bool {
//     // set up vectors to mock persistent memory
//     let mut region_sizes = Vec::<u64>::new();
//     region_sizes.push(512);
//     region_sizes.push(512);
//     let mut regions = VolatileMemoryMockingPersistentMemoryRegions::new(region_sizes.as_slice());

//     let result = MultiLogImpl::setup(&mut regions);
//     let (_log_capacities, multilog_id) = match result {
//         Ok((log_capacities, multilog_id)) => (log_capacities, multilog_id),
//         Err(_) => return false,
//     };

//     // start the log
//     let result = MultiLogImpl::start(regions, multilog_id);
//     let mut multilog = match result {
//         Ok(multilog) => multilog,
//         Err(_) => return false,
//     };

//     let mut vec = Vec::new();
//     vec.push(1); vec.push(2); vec.push(3);

//     let result1 = multilog.tentatively_append(0, vec.as_slice());
//     let result2 = multilog.tentatively_append(1, vec.as_slice());
//     match (result1, result2) {
//         (Ok(_), Ok(_)) => {},
//         _=> return false,
//     }

//     let result = multilog.commit();
//     match result {
//         Ok(_) => {},
//         _ => return false,
//     }

//     let result = multilog.advance_head(0, 2);
//     match result {
//         Ok(_) => {}
//         _ => return false
//     }

//     true
// }

// fn test_multilog_on_memory_mapped_file() -> Option<()>
// {
//     // To test the multilog, we use files in the current directory that mock persistent-memory
//     // regions. Here we use such regions, one of size 4096 and one of size 1024.
//     let mut region_sizes: Vec<u64> = Vec::<u64>::new();
//     region_sizes.push(4096);
//     region_sizes.push(1024);

//     // Create the multipersistent memory out of the two regions.
//     let file_name = "test_multilog";
//     #[cfg(target_os = "windows")]
//     let mut pm_regions = FileBackedPersistentMemoryRegions::new(
//         &file_name,
//         MemoryMappedFileMediaType::SSD,
//         region_sizes.as_slice(),
//         FileCloseBehavior::TestingSoDeleteOnClose
//     ).ok()?;
//     #[cfg(target_os = "linux")]
//     let mut pm_regions = FileBackedPersistentMemoryRegions::new(
//         &file_name,
//         region_sizes.as_slice(),
//         PersistentMemoryCheck::DontCheckForPersistentMemory,
//     ).ok()?;

//     // Set up the memory regions to contain a multilog. The capacities will be less
//     // than 4096 and 1024 because a few bytes are needed in each region for metadata.
//     let (capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions).ok()?;
//     runtime_assert(capacities.len() == 2);
//     runtime_assert(capacities[0] <= 4096);
//     runtime_assert(capacities[1] <= 1024);

//     // Start accessing the multilog.
//     let mut multilog = MultiLogImpl::start(pm_regions, multilog_id).ok()?;

//     // Tentatively append [30, 42, 100] to log #0 of the multilog.
//     let mut v: Vec<u8> = Vec::<u8>::new();
//     v.push(30); v.push(42); v.push(100);
//     let pos = multilog.tentatively_append(0, v.as_slice()).ok()?;
//     runtime_assert(pos == 0);

//     // Note that a tentative append doesn't actually advance the tail. That
//     // doesn't happen until the next commit.
//     let (head, tail, _capacity) = multilog.get_head_tail_and_capacity(0).ok()?;
//     runtime_assert(head == 0);
//     runtime_assert(tail == 0);

//     // Also tentatively append [30, 42, 100, 152] to log #1. This still doesn't
//     // commit anything to the log.
//     v.push(152);
//     let pos = multilog.tentatively_append(1, v.as_slice()).ok()?;
//     runtime_assert(pos == 0);

//     // Now commit the tentative appends. This causes log #0 to have tail 3
//     // and log #1 to have tail 4.
//     if multilog.commit().is_err() {
//         runtime_assert(false); // can't fail
//     }
//     match multilog.get_head_tail_and_capacity(0) {
//         Ok((head, tail, _capacity)) => {
//             runtime_assert(head == 0);
//             runtime_assert(tail == 3);
//         },
//         _ => runtime_assert(false) // can't fail
//     }
//     match multilog.get_head_tail_and_capacity(1) {
//         Ok((head, tail, _capacity)) => {
//             runtime_assert(head == 0);
//             runtime_assert(tail == 4);
//         },
//         _ => runtime_assert(false) // can't fail
//     }

//     // We read the 2 bytes starting at position 1 of log #0. We should
//     // read bytes [42, 100]. This is only guaranteed if the memory
//     // wasn't corrupted.
//     if let Ok(bytes) = multilog.read(0, 1, 2) {
//         runtime_assert(bytes.len() == 2);
//         assert(multilog.constants().impervious_to_corruption() ==> bytes[0] == 42);
//     }

//     // We now advance the head of log #0 to position 2. This causes the
//     // head to become 2 and the tail stays at 3.
//     match multilog.advance_head(0, 2) {
//         Ok(()) => runtime_assert(true),
//         _ => runtime_assert(false) // can't fail
//     }
//     match multilog.get_head_tail_and_capacity(0) {
//         Ok((head, tail, _capacity)) => {
//             runtime_assert(head == 2);
//             runtime_assert(tail == 3);
//         },
//         _ => runtime_assert(false) // can't fail
//     }

//     // If we read from position 2 of log #0, we get the same thing we
//     // would have gotten before the advance-head operation.
//     if let Ok(_bytes) = multilog.read(0, 2, 1) {
//         assert(multilog.constants().impervious_to_corruption() ==> _bytes[0] == 100);
//     }

//     // But if we try to read from position 0 of log #0, we get an
//     // error because we're not allowed to read from before the head.
//     match multilog.read(0, 0, 1) {
//         Err(MultiLogErr::CantReadBeforeHead{head}) => runtime_assert(head == 2),
//         _ => runtime_assert(false) // can't succeed, and can't fail with any other error
//     }
//     Some(())
// }

// fn test_log_on_memory_mapped_file() -> Option<()>
// {
//     let region_size = 1024;

//     // Create the memory out of a single file.
//     let file_name = "test_log";
//     #[cfg(target_os = "windows")]
//     let mut pm_region = FileBackedPersistentMemoryRegion::new(
//         &file_name, MemoryMappedFileMediaType::SSD,
//         region_size,
//         FileCloseBehavior::TestingSoDeleteOnClose
//     ).ok()?;
//     #[cfg(target_os = "linux")]
//     let mut pm_region = FileBackedPersistentMemoryRegion::new(
//         &file_name,
//         region_size,
//         PersistentMemoryCheck::DontCheckForPersistentMemory,
//     ).ok()?;

//     // Set up the memory region to contain a log. The capacity will be less than
//     // the file size because a few bytes are needed for metadata.
//     let (capacity, log_id) = LogImpl::setup(&mut pm_region).ok()?;
//     runtime_assert(capacity <= 1024);

//     // Start accessing the log.
//     let mut log = LogImpl::start(pm_region, log_id).ok()?;

//     // Tentatively append [30, 42, 100] to the log.
//     let mut v: Vec<u8> = Vec::<u8>::new();
//     v.push(30); v.push(42); v.push(100);
//     let pos = log.tentatively_append(v.as_slice()).ok()?;
//     runtime_assert(pos == 0);

//     // Note that a tentative append doesn't actually advance the tail. That
//     // doesn't happen until the next commit.
//     let (head, tail, _capacity) = log.get_head_tail_and_capacity().ok()?;
//     runtime_assert(head == 0);
//     runtime_assert(tail == 0);

//     // Now commit the tentative appends. This causes the log to have tail 3.
//     if log.commit().is_err() {
//         runtime_assert(false); // can't fail
//     }
//     match log.get_head_tail_and_capacity() {
//         Ok((head, tail, _capacity)) => {
//             runtime_assert(head == 0);
//             runtime_assert(tail == 3);
//         },
//         _ => runtime_assert(false) // can't fail
//     }

//     // We read the 2 bytes starting at position 1 of the log. We should
//     // read bytes [42, 100]. This is only guaranteed if the memory
//     // wasn't corrupted.
//     if let Ok(bytes) = log.read(1, 2) {
//         runtime_assert(bytes.len() == 2);
//         proof {
//             if log.constants().impervious_to_corruption() {
//                 log.constants().maybe_corrupted_zero(bytes@, log@.read(1, 2));
//             }
//         }
//         assert(log.constants().impervious_to_corruption() ==> bytes[0] == 42);
//     }

//     // We now advance the head of the log to position 2. This causes the
//     // head to become 2 and the tail stays at 3.
//     match log.advance_head(2) {
//         Ok(()) => runtime_assert(true),
//         _ => runtime_assert(false) // can't fail
//     }
//     match log.get_head_tail_and_capacity() {
//         Ok((head, tail, capacity)) => {
//             runtime_assert(head == 2);
//             runtime_assert(tail == 3);
//         },
//         _ => runtime_assert(false) // can't fail
//     }

//     // If we read from position 2 of the log, we get the same thing we
//     // would have gotten before the advance-head operation.
//     if let Ok(bytes) = log.read(2, 1) {
//         proof {
//             if log.constants().impervious_to_corruption() {
//                 log.constants().maybe_corrupted_zero(bytes@, log@.read(2, 1));
//             }
//         }
//         assert(log.constants().impervious_to_corruption() ==> bytes[0] == 100);
//     }

//     // But if we try to read from position 0, we get an
//     // error because we're not allowed to read from before the head.
//     match log.read(0, 1) {
//         Err(LogErr::CantReadBeforeHead{head}) => runtime_assert(head == 2),
//         Err(LogErr::PmemErr { err: PmemError::AccessOutOfRange }) => {}
//         _ => runtime_assert(false) // can't succeed, and can't fail with any other error
//     }
//     Some(())
// }

#[repr(C)]
#[derive(PmCopy, Copy, Debug, Hash)]
struct TestKey {
    val: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct TestItem {
    val: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct TestListElement {
    val: u64,
}

#[verifier::external_body]
fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}

/* Temporarily commented out for subregion development
fn test_durable_on_memory_mapped_file() {
    assume(false);

    let region_size = 4096;
    let log_file_name = "/home/hayley/kv_files/test_log";
    let metadata_file_name = "/home/hayley/kv_files/test_metadata";
    let item_table_file_name = "/home/hayley/kv_files/test_item";
    let list_file_name = "/home/hayley/kv_files/test_list";

    let num_keys = 16;
    let node_size = 16;

    // delete the test files if they already exist. Ignore the result,
    // since it's ok if the files don't exist.
    remove_file(log_file_name);
    remove_file(metadata_file_name);
    remove_file(item_table_file_name);
    remove_file(list_file_name);

    // Create a file, and a PM region, for each component
    let mut log_region = create_pm_region(log_file_name, region_size);
    let mut metadata_region = create_pm_region(metadata_file_name, region_size);
    let mut item_table_region = create_pm_region(item_table_file_name, region_size);
    let mut list_region = create_pm_region(list_file_name, region_size);

    let kvstore_id = generate_fresh_log_id();
    DurableKvStore::<_, TestKey, TestItem, TestListElement>::setup(&mut metadata_region, &mut item_table_region, &mut list_region, &mut log_region, 
        kvstore_id, num_keys, node_size).unwrap();

    let mut log_wrpm = WriteRestrictedPersistentMemoryRegion::<TrustedPermission, _>::new(log_region);
    let mut metadata_wrpm = WriteRestrictedPersistentMemoryRegion::<TrustedMetadataPermission, _>::new(metadata_region);
    let mut item_wrpm = WriteRestrictedPersistentMemoryRegion::<TrustedItemTablePermission, _>::new(item_table_region);
    let mut list_wrpm = WriteRestrictedPersistentMemoryRegion::<TrustedListPermission, _>::new(list_region);
    let tracked fake_kv_permission = TrustedKvPermission::<_, TestKey, TestItem, TestListElement>::fake_kv_perm();
    let (mut kv_store, _) = DurableKvStore::<_, TestKey, TestItem, TestListElement>::start(metadata_wrpm, item_wrpm, list_wrpm, log_wrpm, kvstore_id, num_keys, node_size, Tracked(&fake_kv_permission)).unwrap();

    let key1 = TestKey { val: 0 };
    let key2 = TestKey { val: 1 };

    let item1 = TestItem { val: 10 };
    let item2 = TestItem { val: 20 };

    // Create a few kv pairs 
    let (key1_index, list1_index) = kv_store.tentative_create(&key1, &item1, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    let (key2_index, list2_index) = kv_store.tentative_create(&key2, &item2, kvstore_id, Tracked(&fake_kv_permission)).unwrap();

    // We should not be able to read items or lists from uncommitted records
    let read_item1 = kv_store.read_item(kvstore_id, key1_index);
    let read_item2 = kv_store.read_item(kvstore_id, key2_index);
    runtime_assert(read_item1.is_err());
    runtime_assert(read_item2.is_err());
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).is_err());
    runtime_assert(kv_store.get_list_len(kvstore_id, key2_index).is_err());

    // Commit the transaction -- this should succeed, and we should then be able to read the items
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    let read_item1: Box<TestItem> = kv_store.read_item(kvstore_id, key1_index).unwrap();
    let read_item2 = kv_store.read_item(kvstore_id, key2_index).unwrap();

    // we can't directly compare the items(?) but they only have one field, so we compare the fields
    runtime_assert(read_item1.val == item1.val);
    runtime_assert(read_item2.val == item2.val);

    // `create` sets up an empty list for each record. Make sure that the lists both have a length of 0
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 0);
    runtime_assert(kv_store.get_list_len(kvstore_id, key2_index).unwrap() == 0);

    // check that attempting to access an invalid index results in an error
    let invalid_index = 0;
    // since we don't have control over the indices assigned to the keys, fail the test here if we accidentally collide
    // to make it easier to differentiate between an actual failure and a collision
    runtime_assert(invalid_index != key1_index && invalid_index != key2_index);
    runtime_assert(kv_store.read_item(kvstore_id, invalid_index).is_err());
    runtime_assert(kv_store.get_list_len(kvstore_id, invalid_index).is_err());

    // Try to update one of the items
    let item3 = TestItem { val: 13 };
    kv_store.tentative_update_item(key1_index, kvstore_id, &item3).unwrap();
    // We shouldn't be able to read the new item yet -- reading should return the old value
    let read_item3 = kv_store.read_item(kvstore_id, key1_index).unwrap();
    runtime_assert(read_item3.val == item1.val);

    // After committing the transaction, reading the item should return the new value
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    let read_item3 = kv_store.read_item(kvstore_id, key1_index).unwrap();
    runtime_assert(read_item3.val == item3.val);

    // check that deleting an item succeeds and works correctly
    kv_store.tentative_delete(key2_index, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    // until we commit the delete, the item should still be visible
    let read_item4 = kv_store.read_item(kvstore_id, key2_index).unwrap();
    runtime_assert(read_item4.val == item2.val);

    // after committing, the record is no longer present
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    runtime_assert(kv_store.read_item(kvstore_id, key2_index).is_err());
    runtime_assert(kv_store.get_list_len(kvstore_id, key2_index).is_err());

    // append a list element
    let list_elem1 = TestListElement { val: 100 };
    kv_store.tentative_append(key1_index, &list_elem1, 
        list1_index, 0, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    
    // before commit, the list length should be 0
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 0);
    // TODO: read fns will currently read whatever is at the specified location (and most likely return a CRC
    // mismatch error if it's invalid); I plan to handle management of which locations are valid in volatile state

    // after commit, list length should be 1, and we should be able to read the list element
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 1);
    let read_list_elem1 = kv_store.read_list_entry_at_index(list1_index, 0, kvstore_id).unwrap();
    assert(read_list_elem1.val == list_elem1.val);

    // check that we can allocate a list node. this doesn't change visible state,
    // but the operation should succeed
    kv_store.tentative_alloc_list_node(key1_index, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();

    // we should be able to update an existing list entry 
    let list_elem2 = TestListElement { val: 15 };
    kv_store.tentative_update_list_entry_at_index(list1_index, 0, list_elem2, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    // the new list element should not be visible yet
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 1);
    let read_list_elem1 = kv_store.read_list_entry_at_index(list1_index, 0, kvstore_id).unwrap();
    assert(read_list_elem1.val == list_elem1.val); 

    // after commit, the list length should be the same but the contents of the list changed
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 1);
    let read_list_elem2 = kv_store.read_list_entry_at_index(list1_index, 0, kvstore_id).unwrap();
    assert(read_list_elem2.val == list_elem2.val); 

    // trimming the list should succeed
    kv_store.tentative_trim_list(key1_index, list1_index, list1_index, 1, 1, kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 1);
    kv_store.commit(kvstore_id, Tracked(&fake_kv_permission)).unwrap();
    runtime_assert(kv_store.get_list_len(kvstore_id, key1_index).unwrap() == 0);

}

fn test_kv_on_memory_mapped_file() {
    assume(false);

    let region_size = 4096;
    let log_file_name = "/home/hayley/kv_files/test_log";
    let metadata_file_name = "/home/hayley/kv_files/test_metadata";
    let item_table_file_name = "/home/hayley/kv_files/test_item";
    let list_file_name = "/home/hayley/kv_files/test_list";

    let num_keys = 16;
    let node_size = 16;

    // delete the test files if they already exist. Ignore the result,
    // since it's ok if the files don't exist.
    remove_file(log_file_name);
    remove_file(metadata_file_name);
    remove_file(item_table_file_name);
    remove_file(list_file_name);

    // Create a file, and a PM region, for each component
    let mut log_region = create_pm_region(log_file_name, region_size);
    let mut metadata_region = create_pm_region(metadata_file_name, region_size);
    let mut item_table_region = create_pm_region(item_table_file_name, region_size);
    let mut list_region = create_pm_region(list_file_name, region_size);

    let kvstore_id = generate_fresh_log_id();

    UntrustedKvStoreImpl::<_, TestKey, TestItem, TestListElement, VolatileKvIndexImpl<TestKey>>::untrusted_setup(&mut metadata_region, &mut item_table_region, &mut list_region, &mut log_region, kvstore_id, num_keys, node_size).unwrap();

    let mut kv = UntrustedKvStoreImpl::<_, TestKey, TestItem, TestListElement, VolatileKvIndexImpl<TestKey>>::untrusted_start(metadata_region, item_table_region, list_region, log_region, kvstore_id, num_keys, node_size).unwrap();

    let key1 = TestKey { val: 0 };
    let key2 = TestKey { val: 1 };

    let item1 = TestItem { val: 10 };
    let item2 = TestItem { val: 20 };

    // create a record
    let tracked fake_kv_perm = TrustedKvPermission::fake_kv_perm();
    kv.untrusted_create(&key1, &item1, kvstore_id, Tracked(&fake_kv_perm)).unwrap();

    // read the item of the record we just created
    let read_item1 = kv.untrusted_read_item(&key1).unwrap();
    assert(read_item1.val == item1.val);

}

fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
{
    assume(false);
    #[cfg(target_os = "windows")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name, MemoryMappedFileMediaType::SSD,
        region_size,
        FileCloseBehavior::TestingSoDeleteOnClose
    ).unwrap();
    #[cfg(target_os = "linux")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    ).unwrap();

    pm_region
}

*/

#[allow(dead_code)]
fn main()
{
    // test_multilog_in_volatile_memory();
    // test_multilog_on_memory_mapped_file();
    // test_log_on_memory_mapped_file();
    // test_durable_on_memory_mapped_file();
}
}
