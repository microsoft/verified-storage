use storage_node::kv::kvimpl_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use serde::Deserialize;
use std::fs;
use std::env;

use std::collections::HashMap;
use std::collections::BTreeMap;

const MAX_KEY_LEN: usize = 1024;
const MAX_ITEM_LEN: usize = 1140; 
const KVSTORE_ID: u128 = 500;

// stop indicator for magic-trace
#[no_mangle]
fn capybarakv_stop_indicator() {}

#[derive(Deserialize, Debug)]
struct Config {
    config: DbOptions,
}

#[derive(Deserialize, Debug)]
struct DbOptions {
    kv_file: String,
    node_size: u32, 
    num_keys: u64, 
    region_size: u64, 
    threads: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug, Hash, Ord, PartialOrd)]
struct YcsbKey {
    key: [i8; MAX_KEY_LEN],
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct YcsbItem {
    item: [i8; MAX_ITEM_LEN]
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct TestListElement {
    val: u64,
}

fn parse_configs(config_file: String) -> DbOptions {
    println!("{:?}", chrono::offset::Local::now());
    println!("Reading configs from {:?}", config_file);
    let config_contents = match fs::read_to_string(&config_file) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Could not read file `{}`: {}", config_file, e);
            panic!();
        }
    };

    // TODO: Proper error handling of invalid config files
    let config: Config = toml::from_str(&config_contents).unwrap();
    println!("config: {:?}", config);
    config.config
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let config_file = if args.len() > 1 {
        args[1].clone()
    } else {
        "capybarakv_config.toml".to_string()
    };
    let workload = if args.len() > 2 {
        args[2].clone()
    } else {
        println!("Please specify a test to run");
        return;
    };

    if workload == "insert" {
        insert_test(config_file);
    } else if workload == "hash" {
        hash_test();
    } else if workload == "btree" {
        btree_test();
    }

}

fn insert_test(config_file: String) {
    let config = parse_configs(config_file);

    remove_file(&config.kv_file);

    let mut kv_region = create_pm_region(&config.kv_file, config.region_size);
    KvStore::<_, YcsbKey, YcsbItem, TestListElement>::setup(
        &mut kv_region, KVSTORE_ID, config.num_keys, config.node_size, 1).unwrap();

    let kv_region = open_pm_region(&config.kv_file, config.region_size);

    let mut kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement>::start(kv_region, KVSTORE_ID).unwrap();

    let item = YcsbItem { item: [ 0; MAX_ITEM_LEN] };

    println!("Inserting items");
    let mut keys_vec = Vec::with_capacity(config.num_keys.try_into().unwrap());
    for i in 0..config.num_keys {
        let key_string = format!("key{:?}", i);
        let key_bytes = key_string.as_bytes();
        let key_bytes_i8 = unsafe { std::slice::from_raw_parts(key_bytes.as_ptr() as *const i8, key_bytes.len()) };
        let mut byte_array = [0i8; MAX_KEY_LEN];
        byte_array[0..key_bytes.len()].copy_from_slice(key_bytes_i8);
        let key = YcsbKey { key: byte_array };
        
        kv.create(&key, &item).unwrap();
        kv.commit().unwrap();
        keys_vec.push(key);
        capybarakv_stop_indicator();
    }

    println!("Reading items");
    for k in keys_vec {
        kv.read_item(&k).unwrap();
        capybarakv_stop_indicator();
    }
}

fn hash_test() {
    // this doesn't use capybarakv, it's just to try to get an idea of whether hashmaps
    // or btreemaps are faster for what we want to do

    let mut map = HashMap::new();
    let item = YcsbItem { item: [ 0; MAX_ITEM_LEN] };

    let num_keys = 50000;
    println!("Inserting keys in HashMap");

    for i in 0..num_keys {
        let key_string = format!("key{:?}", i);
        let key_bytes = key_string.as_bytes();
        let key_bytes_i8 = unsafe { std::slice::from_raw_parts(key_bytes.as_ptr() as *const i8, key_bytes.len()) };
        let mut byte_array = [0i8; MAX_KEY_LEN];
        byte_array[0..key_bytes.len()].copy_from_slice(key_bytes_i8);
        let key = YcsbKey { key: byte_array };
        
        map.insert(key, &item);
    }
}

fn btree_test() {
     // this doesn't use capybarakv, it's just to try to get an idea of whether hashmaps
    // or btreemaps are faster for what we want to do

    let mut map = BTreeMap::new();
    let item = YcsbItem { item: [ 0; MAX_ITEM_LEN] };

    let num_keys = 50000;
    println!("Inserting keys in HashMap");

    for i in 0..num_keys {
        let key_string = format!("key{:?}", i);
        let key_bytes = key_string.as_bytes();
        let key_bytes_i8 = unsafe { std::slice::from_raw_parts(key_bytes.as_ptr() as *const i8, key_bytes.len()) };
        let mut byte_array = [0i8; MAX_KEY_LEN];
        byte_array[0..key_bytes.len()].copy_from_slice(key_bytes_i8);
        let key = YcsbKey { key: byte_array };
        
        map.insert(key, &item);
    }
}

fn open_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
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


fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
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


fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
