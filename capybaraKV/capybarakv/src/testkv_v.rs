use vstd::prelude::*;

use crate::common::util_v::*;
use crate::kv2::concurrentspec_t::*;
use crate::kv2::impl_t::KvStore;
use crate::kv2::rwkv_t::*;
use crate::kv2::rwkv_v::*;
use crate::kv2::shardkv_t;
use crate::kv2::shardkv_t::*;
use crate::kv2::shardkv_v::*;
use crate::kv2::spec_t::{AtomicKvStore, KvError, LogicalRange, LogicalRangeGapsPolicy, RecoveredKvStore,
                         SetupParameters};
// use crate::log::logimpl_t::*;
// use crate::multilog::layout_v::*;
// use crate::multilog::multilogimpl_t::*;
// use crate::multilog::multilogimpl_v::*;
// use crate::multilog::multilogspec_t::*;
#[cfg(all(target_os = "linux", feature = "pmem"))]
use crate::pmem::linux_pmemfile_t::*;
#[cfg(all(target_os = "linux", not(feature = "pmem")))]
use crate::pmem::mmap_pmemfile_t::*;
#[cfg(target_os = "windows")]
use crate::pmem::windows_pmemfile_t::*;
#[cfg(target_os = "macos")]
use crate::pmem::mmap_pmemfile_t::*;
#[cfg(target_os = "macos")]
use crate::pmem::mmap_pmemfile_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemmock_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use crate::pmem::power_t::*;
use pmcopy::PmCopy;
use rand::Rng;
use std::hash::Hash;
use std::collections::VecDeque;
use vstd::pcm::*;
use vstd::pervasive::runtime_assert;
use vstd::tokens::frac::*;

verus! {

#[verifier::external_body]
pub exec fn generate_fresh_id() -> (out: u128)
{
    rand::thread_rng().gen::<u128>()
}

// These definitions test PmCopy-generated static assertions for various different types
#[repr(C)]
#[derive(PmCopy, Copy)]
union TestUnion {
    a: u8,
    b: u64,
    c: u128
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum1 {
    V1,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum2 {
    V1,
    V2,
    V3, 
    V4
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum3 {
    V1(u16),
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum4 {
    V1(u16),
    V2(u8),
    V3(u64),
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum5 {
    V1,
    V2(u128),
    V3(u32),
}

#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum6 {
    V1 {f0: u64, f1: u8, f3: u128, f4: u16}
}

#[allow(inconsistent_fields)]
#[repr(C)]
#[derive(PmCopy, Copy)]
enum TestEnum7 {
    V1 {f0: u64, f1: u8, f3: u128, f4: u16},
    V2,
    V3(u16),
    V4 {f0: u128, f1: u16}
}

// #[repr(C,u8)]
// #[derive(PmCopy, Copy)]
// enum TestEnum8 {
//     V1,
// }

#[repr(C)]
#[derive(PmCopy, Copy)]
struct TestUnnamedFieldStruct(u8, u128, u16);


pub type PmemOffset = u128;
#[repr(C)]
#[derive(Copy, Debug, PmCopy)]
pub enum BlockOffsetType {
    None,
    InPMem(PmemOffset),
    InFile,
}

// // this function is defined outside of the test module so that we can both
// // run verification on it and call it in a test to ensure that all operations
// // succeed
// #[allow(dead_code, unused_variables, unused_mut)]
// pub fn test_multilog_in_volatile_memory() -> bool {
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

// pub fn test_multilog_on_memory_mapped_file() -> Option<()>
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

// pub fn test_log_on_memory_mapped_file() -> Option<()>
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
pub struct TestKey {
    pub val: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
pub struct TestItem {
    pub val: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
pub struct TestListElement {
    pub val: u64,
    pub start: usize,
    pub end: usize
}

impl LogicalRange for TestListElement {
    open spec fn spec_start(&self) -> usize
    {
        self.start
    }

    open spec fn spec_end(&self) -> usize
    {
        self.end
    }

    fn start(&self) -> usize
    {
        self.start
    }

    fn end(&self) -> usize
    {
        self.end
    }
}

#[verifier::external_body]
fn print_message(msg: &'static str) {
    println!("{}", msg);
}

#[verifier::external_body]
fn print_result(msg: &'static str, value: u32) {
    println!("{}: {value}", msg);
}

#[verifier::external_body]
fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}

fn create_pm_region(file_name: &str, region_size: u64) -> (result: Result<FileBackedPersistentMemoryRegion, PmemError>)
    ensures
        result matches Ok(pm) ==> pm.inv(),
{
    #[cfg(target_os = "windows")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name, MemoryMappedFileMediaType::SSD,
        region_size,
        FileCloseBehavior::TestingSoDeleteOnClose
    );
    #[cfg(all(target_os = "linux", feature = "pmem"))]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    );
    #[cfg(all(target_os = "linux", not(feature = "pmem")))]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
    );
    #[cfg(target_os = "macos")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
    );

    pm_region
}

/* Temporarily commented out for subregion development
pub fn test_durable_on_memory_mapped_file() {
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

    let mut log_powerpm = PoWERPersistentMemoryRegion::<TrustedPermission, _>::new(log_region);
    let mut metadata_powerpm = PoWERPersistentMemoryRegion::<TrustedMetadataPermission, _>::new(metadata_region);
    let mut item_powerpm = PoWERPersistentMemoryRegion::<TrustedItemTablePermission, _>::new(item_table_region);
    let mut list_powerpm = PoWERPersistentMemoryRegion::<TrustedListPermission, _>::new(list_region);
    let tracked fake_kv_permission = TrustedKvPermission::<_, TestKey, TestItem, TestListElement>::fake_kv_perm();
    let (mut kv_store, _) = DurableKvStore::<_, TestKey, TestItem, TestListElement>::start(metadata_powerpm, item_powerpm, list_powerpm, log_powerpm, kvstore_id, num_keys, node_size, Tracked(&fake_kv_permission)).unwrap();

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
*/

pub fn test_kv_on_memory_mapped_file() -> Result<(), ()>
{
    let kv_file_name = "test_kv";

    let max_keys = 16;
    let max_list_elements = 16;

    // delete the test file if it already exists. Ignore the result,
    // since it's ok if the file doesn't exist.
    remove_file(kv_file_name);

    let kvstore_id = generate_fresh_id();

    let ps = SetupParameters{
        kvstore_id,
        logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsForbidden,
        max_keys,
        max_list_elements,
        max_operations_per_transaction: 4,
    };
   let region_size = match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>
        ::space_needed_for_setup(&ps) {
        Ok(s) => s,
        Err(e) => { print_message("Failed to compute space needed for setup"); return Err(()); },
   };

    let mut pm = match create_pm_region(&kv_file_name, region_size) {
        Ok(p) => p,
        Err(e) => { print_message("Failed to create file for kv store"); return Err(()); },
    };

    assume(vstd::std_specs::hash::obeys_key_model::<TestKey>());
    match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>::setup(&mut pm, &ps) {
        Ok(()) => {},
        Err(e) => { print_message("Failed to set up KV store"); return Err(()); },
    }

    let mut kv = match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>
        ::start(pm, kvstore_id) {
        Ok(kv) => kv,
        Err(e) => { print_message("Failed to start KV store"); return Err(()); },
    };

    let key1 = TestKey { val: 0x33333333 };
    let key2 = TestKey { val: 0x44444444 };

    let item1 = TestItem { val: 0x55555555 };
    let item2 = TestItem { val: 0x66666666 };

    // create a record
    match kv.tentatively_create(&key1, &item1) {
        Ok(()) => {},
        Err(e) => { print_message("Error when creating key 1"); return Err(()); }
    }
    match kv.commit() {
        Ok(()) => { },
        Err(e) => { print_message("Error when committing"); return Err(()); }
    }

    // read the item of the record we just created
    let read_item1 = match kv.read_item(&key1) {
        Ok(i) => i,
        Err(e) => { print_message("Error when reading key"); return Err(()); },
    };

    runtime_assert(read_item1.val == item1.val);

    match kv.read_item(&key2) {
        Ok(i) => { print_message("Error: failed to fail when reading non-inserted key"); return Err(()); },
        Err(KvError::KeyNotFound) => {},
        Err(e) => { print_message("Error: got an unexpected error when reading non-inserted key"); return Err(()); },
    }

    print_message("All kv operations gave expected results");
    return Ok(());
}

impl ReadLinearizer<TestKey, TestItem, TestListElement, ReadItemOp<TestKey>>
    for GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>
{
    type Completion = Self;

    open spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    open spec fn pre(self, id: int, op: ReadItemOp<TestKey>) -> bool
    {
        &&& self.id() == id
    }

    open spec fn post(
        self,
        completion: Self,
        id: int,
        op: ReadItemOp<TestKey>,
        result: Result<TestItem, KvError>,
    ) -> bool
    {
        &&& completion == self
        &&& op.result_valid(self@, result)
    }

    proof fn apply(
        tracked self,
        op: ReadItemOp<TestKey>,
        result: Result<TestItem, KvError>,
        tracked r: &GhostVarAuth<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>
    ) -> tracked Self::Completion
    {
        r.agree(&self);
        self
    }
}

struct TestMutatingLinearizer<Op>
where
    Op: MutatingOperation<TestKey, TestItem, TestListElement>
{
    r: GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>,
    ghost op: Op,
    ghost old_ckv: Option<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>,
    ghost new_ckv: Option<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>,
    ghost powerpm_id: int,
}

impl<Op> MutatingLinearizer<TestKey, TestItem, TestListElement, Op>
    for TestMutatingLinearizer<Op>
where
    Op: MutatingOperation<TestKey, TestItem, TestListElement>
{
    type Completion = Self;

    closed spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    closed spec fn pre(self, id: int, op: Op) -> bool
    {
        &&& self.r.id() == id
        &&& self.op == op
        &&& self.old_ckv is None
        &&& self.new_ckv is None
    }

    closed spec fn post(
        self,
        complete: Self::Completion,
        id: int,
        op: Op,
        exec_result: Result<Op::KvResult, KvError>,
    ) -> bool
    {
        &&& complete.r.id() == self.r.id()
        &&& complete.r.id() == id
        &&& self.op == op
        &&& complete.old_ckv matches Some(old_ckv)
        &&& complete.new_ckv matches Some(new_ckv)
        &&& op.result_valid(old_ckv, new_ckv, exec_result)
    }

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<TestKey, TestItem, TestListElement>,
        exec_result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>
    ) -> (tracked complete: Self::Completion)
    {
        let tracked mut mself = self;
        mself.old_ckv = Some(r@);
        mself.new_ckv = Some(new_ckv);
        r.update(&mut mself.r, new_ckv);
        mself
    }
}

pub fn test_concurrent_kv_on_memory_mapped_file() -> Result<(), ()>
{
    let kv_file_name = "test_concurrent_kv";

    let max_keys = 16;
    let max_list_elements = 16;

    // delete the test file if it already exists. Ignore the result,
    // since it's ok if the file doesn't exist.
    remove_file(kv_file_name);

    let kvstore_id = generate_fresh_id();

    let ps = SetupParameters{
        kvstore_id,
        logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsForbidden,
        max_keys,
        max_list_elements,
        max_operations_per_transaction: 4,
    };
   let region_size = match ConcurrentKvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>
        ::space_needed_for_setup(&ps) {
        Ok(s) => s,
        Err(e) => { print_message("Failed to compute space needed for setup"); return Err(()); },
   };

    let mut pm = match create_pm_region(&kv_file_name, region_size) {
        Ok(p) => p,
        Err(e) => { print_message("Failed to create file for kv store"); return Err(()); },
    };

    assume(vstd::std_specs::hash::obeys_key_model::<TestKey>());
    let ghost pm_constants = pm.constants();
    let mut ckv;
    let tracked mut gvar;
    match crate::kv2::rwkv_t::setup::<FileBackedPersistentMemoryRegion, TestKey,
                                      TestItem, TestListElement>(pm, &ps, Ghost(123)) {
        Ok((ckv0, gvar0)) => {
            ckv = ckv0;
            proof { gvar = gvar0; }
        },
        Err(e) => { print_message("Failed to set up KV store"); return Err(()); },
    };

    let key1 = TestKey { val: 0x33333333 };
    let key2 = TestKey { val: 0x44444444 };

    let item1 = TestItem { val: 0x55555555 };
    let item2 = TestItem { val: 0x66666666 };

    let tracked app_resource = gvar.get();
    let ghost op = CreateOp::<TestKey, TestItem, true>{ key: key1, item: item1 };
    let tracked mut create_linearizer = TestMutatingLinearizer::<CreateOp<TestKey, TestItem, true>>{
        r: app_resource,
        op,
        old_ckv: None,
        new_ckv: None,
        powerpm_id: 0,
    };

    let (create_result, Tracked(create_linearizer)) = ckv.create::<TestMutatingLinearizer<CreateOp<TestKey, TestItem, true>>, true>(
        &key1, &item1, Tracked(create_linearizer)
    );
    match create_result {
        Ok(()) => {},
        Err(e) => { print_message("Error when creating key 1"); return Err(()); },
    };

    let tracked app_resource = create_linearizer.r;

    // read the item of the record we just created
    let (read_item_result, Tracked(app_resource)) = ckv.read_item::<GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>>(
        &key1, Tracked(app_resource)
    );
    let read_item1 = match read_item_result {
        Ok(i) => i,
        Err(e) => { print_message("Error when reading key"); return Err(()); },
    };

    if read_item1.val != item1.val {
        print_message("ERROR: Read incorrect value");
        return Err(());
    }

    print_message("SUCCESS: Read correct value");

    let (read_item_result, Tracked(app_resource)) = ckv.read_item::<GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>>(
        &key2, Tracked(app_resource)
    );
    match read_item_result {
        Ok(i) => { print_message("Error: failed to fail when reading non-inserted key"); return Err(()); },
        Err(KvError::KeyNotFound) => {},
        Err(e) => { print_message("Error: got an unexpected error when reading non-inserted key"); return Err(()); },
    };

    print_message("All kv operations gave expected results");
    return Ok(());
}

pub fn test_sharded_kv_on_memory_mapped_file() -> Result<(), ()>
{
    let kv_file_name0 = "test_concurrent_kv0";
    let kv_file_name1 = "test_concurrent_kv1";

    let max_keys = 16;
    let max_list_elements = 16;

    // delete the test files if they already exist. Ignore the result,
    // since it's ok if the file doesn't exist.
    remove_file(kv_file_name0);
    remove_file(kv_file_name1);

    let kvstore_id = generate_fresh_id();
    let ps = SetupParameters{
        kvstore_id,
        logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsForbidden,
        max_keys,
        max_list_elements,
        max_operations_per_transaction: 4,
    };

    let region_size = match ConcurrentKvStore::<FileBackedPersistentMemoryRegion,
                                                TestKey, TestItem, TestListElement>::space_needed_for_setup(&ps) {
        Ok(s) => s,
        Err(e) => { print_message("Failed to compute space needed for setup"); return Err(()); },
    };

    let mut pm0 = match create_pm_region(&kv_file_name0, region_size) {
        Ok(p) => p,
        Err(e) => { print_message("Failed to create file for kv store 0"); return Err(()); },
    };

    let mut pm1 = match create_pm_region(&kv_file_name1, region_size) {
        Ok(p) => p,
        Err(e) => { print_message("Failed to create file for kv store 1"); return Err(()); },
    };

    assume(vstd::std_specs::hash::obeys_key_model::<TestKey>());
    assume(pm0.constants() == pm1.constants());
    let ghost pm_constants = pm0.constants();
    let ghost shard_namespace = 5;
    let ghost namespace = 6;

    let mut pms = VecDeque::new();
    pms.push_back(pm0);
    pms.push_back(pm1);

    let mut skv;
    let tracked mut gvar;
    match shardkv_t::setup::<FileBackedPersistentMemoryRegion,
                             TestKey, TestItem, TestListElement>(
        pms, &ps, Ghost(pm_constants), Ghost(namespace), Ghost(shard_namespace),
    ) {
        Ok((skv0, gvar0)) => {
            skv = skv0;
            proof { gvar = gvar0; }
        },
        Err(e) => { print_message("Failed to set up KV store 1"); return Err(()); },
    }

    let key1 = TestKey { val: 0x33333333 };
    let key2 = TestKey { val: 0x44444444 };

    let item1 = TestItem { val: 0x55555555 };
    let item2 = TestItem { val: 0x66666666 };

    let tracked app_resource = gvar.get();
    let ghost op = CreateOp::<TestKey, TestItem, false>{ key: key1, item: item1 };
    let tracked mut create_linearizer = TestMutatingLinearizer::<CreateOp<TestKey, TestItem, false>>{
        r: app_resource,
        op,
        old_ckv: None,
        new_ckv: None,
        powerpm_id: 0,
    };

    let (create_result, Tracked(create_linearizer)) = skv.create::<TestMutatingLinearizer<CreateOp<TestKey, TestItem, false>>>(
        &key1, &item1, Tracked(create_linearizer)
    );
    match create_result {
        Ok(()) => {},
        Err(e) => { print_message("Error when creating key 1"); return Err(()); },
    };

    let tracked app_resource = create_linearizer.r;

    // read the item of the record we just created
    let (read_item_result, Tracked(app_resource)) = skv.read_item::<GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>>(
        &key1, Tracked(app_resource)
    );
    let read_item1 = match read_item_result {
        Ok(i) => i,
        Err(e) => { print_message("Error when reading key"); return Err(()); },
    };

    if read_item1.val != item1.val {
        print_message("ERROR: Read incorrect value");
        return Err(());
    }

    print_message("SUCCESS: Read correct value");

    let (read_item_result, Tracked(app_resource)) = skv.read_item::<GhostVar<ConcurrentKvStoreView<TestKey, TestItem, TestListElement>>>(
        &key2, Tracked(app_resource)
    );
    match read_item_result {
        Ok(i) => { print_message("Error: failed to fail when reading non-inserted key"); return Err(()); },
        Err(KvError::KeyNotFound) => {},
        Err(e) => { print_message("Error: got an unexpected error when reading non-inserted key"); return Err(()); },
    };

    print_message("All kv operations gave expected results");
    return Ok(());
}

}
