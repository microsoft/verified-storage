#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

use capybarakv_interface::*;
use storage_node::kv::kvimpl_t::*;
use storage_node::kv::volatile::volatileimpl_v::*;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use std::ffi::CStr;


include!("./bindings.rs");

pub mod capybarakv_interface;
mod microbenchmarks;

const DB_PATH: &CStr = c"/mnt/pmem/";

// stop indicator for magic-trace.
#[no_mangle]
fn capybarakv_stop_indicator() {}

pub fn main() {
    // capybarakv_test();
    rocksdb_test();
}

fn capybarakv_test() {
    let node_size = 16;
    
    let config_file_name: String = "config.toml".to_string();
    let (log_file_name, metadata_file_name, list_file_name, item_table_file_name) = read_filenames(&config_file_name);

    setup_kv(&log_file_name, &metadata_file_name, &list_file_name, &item_table_file_name, node_size);

    // Create a file, and a PM region, for each component
    let log_region = open_pm_region(&log_file_name, REGION_SIZE);
    let metadata_region = open_pm_region(&metadata_file_name, REGION_SIZE);
    let item_table_region = open_pm_region(&item_table_file_name, REGION_SIZE);
    let list_region = open_pm_region(&list_file_name, REGION_SIZE);

    let mut kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::start(
        metadata_region, item_table_region, list_region, log_region, KVSTORE_ID, NUM_KEYS, node_size).unwrap();

    let item = YcsbItem { item: [ 0; MAX_ITEM_LEN] };

    println!("Inserting items");
    let mut keys_vec = Vec::with_capacity(500000);
    for i in 0..500000 {
        let key_string = format!("key{:?}", i);
        let key_bytes = key_string.as_bytes();
        let key_bytes_i8 = unsafe { std::slice::from_raw_parts(key_bytes.as_ptr() as *const i8, key_bytes.len()) };
        let mut byte_array = [0i8; MAX_KEY_LEN];
        byte_array[0..key_bytes.len()].copy_from_slice(key_bytes_i8);
        let key = YcsbKey { key: byte_array };
        
        kv.create(&key, &item, KVSTORE_ID).unwrap();
        keys_vec.push(key);
    }

    println!("Reading items");
    for i in 0..500000 {
        let _item = kv.read_item(&keys_vec[i]).unwrap();
        capybarakv_stop_indicator();
    }
}

fn rocksdb_test() {
    // TODO: move this stuff to a safe wrapper
    let rocksdb_options = unsafe { rocksdb_options_create() };
    let mut err: *mut i8 = core::ptr::null_mut();
    let db = unsafe { rocksdb_open(rocksdb_options, DB_PATH.as_ptr(), &mut err) };
}