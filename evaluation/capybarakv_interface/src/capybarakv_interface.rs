use toml::{Table, Value};
use std::path::Path;

use storage_node::kv::kvimpl_t::*;
use storage_node::kv::volatile::volatileimpl_v::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::{PmSized, PmSafe};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

// pub const MAX_KEY_LEN: usize = 1024;
// pub const MAX_ITEM_LEN: usize = 1140; 
pub const MAX_KEY_LEN: usize = 24;
pub const MAX_ITEM_LEN: usize = 1024; 
pub const REGION_SIZE: u64 = 1024*1024*1024*10; // 20GB
pub const NUM_KEYS: u64 = 500001; 

// use a constant log id so we don't run into issues trying to restore a KV
pub const KVSTORE_ID: u128 = 500;

#[repr(C)]
#[derive(PmSafe, PmSized, Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct YcsbKey {
    pub key: [i8; MAX_KEY_LEN],
}
impl PmCopy for YcsbKey {}


#[repr(C)]
#[derive(PmSafe, PmSized, Copy, Clone, Debug, PartialEq, Eq)]
pub struct YcsbItem {
    pub item: [i8; MAX_ITEM_LEN]
}
impl PmCopy for YcsbItem {}


#[repr(C)]
#[derive(PmSafe, PmSized, Copy, Clone, Debug)]
pub struct TestListElement {
    pub val: u64,
}
impl PmCopy for TestListElement {}

pub fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}

pub struct YcsbKV {
    pub kv: KvStore::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>,
    pub kvstore_id: u128,
}

pub fn read_filenames(config_path: &str) -> (String, String, String, String) {
    let contents = std::fs::read_to_string(config_path).unwrap();
    
    let table = contents.parse::<Table>().unwrap();
    let config_values = &table["config"];

    let kv_directory = if let Value::String(kv_directory) = &config_values["kv_directory"] {
        kv_directory
    } else {
        panic!("invalid toml file");
    };
    let log_file = if let Value::String(log_file) = &config_values["log_file_name"] {
        log_file
    } else {
        panic!("invalid toml file");
    };
    let metadata_file = if let Value::String(metadata_file) = &config_values["metadata_file_name"] {
        metadata_file
    } else {
        panic!("invalid toml file");
    };
    let list_file = if let Value::String(list_file) = &config_values["list_file_name"] {
        list_file
    } else {
        panic!("invalid toml file");
    };
    let item_table_file = if let Value::String(item_table_file) = &config_values["item_table_file_name"] {
        item_table_file
    } else {
        panic!("invalid toml file");
    };
    let log_file_name = Path::new(&kv_directory).join(Path::new(&log_file));
    let log_file_name = log_file_name.to_str().unwrap().to_string();
    let metadata_file_name = Path::new(&kv_directory).join(Path::new(&metadata_file));
    let metadata_file_name = metadata_file_name.to_str().unwrap().to_string();
    let list_file_name = Path::new(&kv_directory).join(Path::new(&list_file));
    let list_file_name = list_file_name.to_str().unwrap().to_string();
    let item_table_file_name = Path::new(&kv_directory).join(Path::new(&item_table_file));
    let item_table_file_name = item_table_file_name.to_str().unwrap().to_string();

    (log_file_name, metadata_file_name, list_file_name, item_table_file_name)
}

pub fn setup_kv(log_file_name: &str, metadata_file_name: &str, list_file_name: &str, item_table_file_name: &str, node_size: u32) {
    // delete the test files if they already exist. Ignore the result,
    // since it's ok if the files don't exist.
    remove_file(&log_file_name);
    remove_file(&metadata_file_name);
    remove_file(&item_table_file_name);
    remove_file(&list_file_name);

    // Create a file, and a PM region, for each component
    let mut log_region = create_pm_region(&log_file_name, REGION_SIZE);
    let mut metadata_region = create_pm_region(&metadata_file_name, REGION_SIZE);
    let mut item_table_region = create_pm_region(&item_table_file_name, REGION_SIZE);
    let mut list_region = create_pm_region(&list_file_name, REGION_SIZE);

    // println!("Setting up KV with {:?} keys, {:?}B nodes, {:?} byte regions", NUM_KEYS, node_size, REGION_SIZE);
    KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::setup(
        &mut metadata_region, &mut item_table_region, &mut list_region, &mut log_region, KVSTORE_ID, NUM_KEYS, node_size).unwrap();
}

pub fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
{
    #[cfg(target_os = "windows")]
    let pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name, MemoryMappedFileMediaType::SSD,
        region_size,
        FileCloseBehavior::TestingSoDeleteOnClose
    ).unwrap();
    #[cfg(target_os = "linux")]
    let pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    ).unwrap();

    pm_region
}


pub fn open_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
{
    #[cfg(target_os = "windows")]
    let pm_region = FileBackedPersistentMemoryRegion::restore(
        &file_name, 
        MemoryMappedFileMediaType::SSD,
        region_size,
    ).unwrap();
    #[cfg(target_os = "linux")]
    let pm_region = FileBackedPersistentMemoryRegion::restore(
        &file_name, 
        region_size
    ).unwrap();

    pm_region
}