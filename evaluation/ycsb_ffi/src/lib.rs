use jni::JNIEnv;
use jni::objects::{JClass, JByteArray};
use jni::sys::jlong;

use storage_node::kv::kvimpl_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::{PmCopy};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use serde::Deserialize;
use std::fs;
use std::env;

const MAX_KEY_LEN: usize = 1024;
const MAX_ITEM_LEN: usize = 1140; 
const MAX_CONFIG_FILE_NAME_LEN: usize = 1024;

// use a constant log id so we don't run into issues trying to restore a KV
const KVSTORE_ID: u128 = 500;

struct YcsbKV {
    kv: KvStore::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement>,
    _kvstore_id: u128,
}

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
}

fn parse_configs(config_file: String) -> DbOptions {
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

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let config_file = if args.len() > 1 {
        args[1].clone()
    } else {
        "capybarakv_config.toml".to_string()
    };

    let config = parse_configs(config_file);

    // delete the test files if they already exist. Ignore the result,
    // since it's ok if the files don't exist.
    remove_file(&config.kv_file);

    // TODO: update kv store to not use reserve any space for list?
    // Create a file, and a PM region, for each component
    let mut kv_region = create_pm_region(&config.kv_file, config.region_size);
    println!("Setting up KV with {:?} keys, {:?}B nodes, {:?}B regions", config.num_keys, config.node_size, config.region_size);
    KvStore::<_, YcsbKey, YcsbItem, TestListElement>::setup(
        &mut kv_region, KVSTORE_ID, config.num_keys, config.node_size, 1).unwrap();
    println!("Done setting up! You can now run YCSB workloads");
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvInit<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>,
    config_file: JByteArray<'local>
) -> jlong {

    let mut file = [0i8; MAX_CONFIG_FILE_NAME_LEN];
    let config_file_name_len: usize = env.get_array_length(&config_file).unwrap().try_into().unwrap();
    if config_file_name_len > MAX_CONFIG_FILE_NAME_LEN {
        let err_str = format!("Error: config file path too long (length {:?}, max {:?})", config_file_name_len, MAX_CONFIG_FILE_NAME_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    }
    let file_name_slice = &mut file[0..config_file_name_len];
    env.get_byte_array_region(config_file, 0, file_name_slice).unwrap();
    let config_file = String::from_utf8(file_name_slice.iter().map(|&c| c as u8).collect()).unwrap();
    let config = parse_configs(config_file);

    // Create a file, and a PM region, for each component
    let kv_region = open_pm_region(&config.kv_file, config.region_size);

    let kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement>::start(kv_region, KVSTORE_ID).unwrap();

    let ret = Box::new(YcsbKV {
        kv,
        _kvstore_id: KVSTORE_ID
    });
    Box::into_raw(ret) as i64
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvCleanup<'local>(_env: JNIEnv<'local>,
    _class: JClass<'local>, input: jlong)
{
    // Ensure the kv store is dropped so that all file descriptors, etc. are cleaned up
    let _ = unsafe { Box::from_raw(input as *mut YcsbKV) };
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvInsert<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>, 
    kv_pointer: jlong, 
    _table: JByteArray<'local>, 
    key: JByteArray<'local>, 
    values: JByteArray<'local>
) {
    // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
    // (otherwise it will be dropped too early)
    let raw_kv_pointer = kv_pointer as *mut YcsbKV;
    let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

    let key_len: usize = env.get_array_length(&key).unwrap().try_into().unwrap();
    let value_len: usize = env.get_array_length(&values).unwrap().try_into().unwrap();
    if key_len > MAX_KEY_LEN {
        let err_str = format!("Error: key too long (length {:?}, max {:?})", key_len, MAX_KEY_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    } 
    if value_len > MAX_ITEM_LEN {
        let err_str = format!("Error: value too long (length {:?}, max {:?})", value_len, MAX_ITEM_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    }

    let ycsb_key = YcsbKey::new(&env, key);
    let ycsb_item = YcsbItem::new(&env, values);

    let ret = kv.kv.create(&ycsb_key, &ycsb_item);
    match ret {
        Ok(_) => {}
        Err(e) => {
            let err_str = format!("Error inserting key: {:?}", e);
            println!("{}", err_str);
            env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        }
    }
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvRead<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>,
    kv_pointer: jlong,
    _table: JByteArray<'local>,
    key: JByteArray<'local>,
) -> JByteArray<'local> {
    // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
    // (otherwise it will be dropped too early)
    let raw_kv_pointer = kv_pointer as *mut YcsbKV;
    let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

    let key_len: usize = env.get_array_length(&key).unwrap().try_into().unwrap();
    if key_len > MAX_KEY_LEN {
        let err_str = format!("Error: key too long (length {:?}, max {:?})", key_len, MAX_KEY_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    } 
    let ycsb_key = YcsbKey::new(&env, key);
    let result = kv.kv.read_item(&ycsb_key);
    match result {
        Ok(item) => {
            match env.byte_array_from_slice(item.as_byte_slice()) {
                Ok(arr) => arr,
                Err(e) => {
                    let err_str = format!("Error getting byte slice: {:?}", e);
                    println!("{}", err_str);
                    env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
                    unreachable!();
                }
            }
        }
        Err(e) => {
            let err_str = format!("Error reading key: {:?}", e);
            println!("{}", err_str);
            env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
            unreachable!();
        }
    }
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvUpdate<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>, 
    kv_pointer: jlong, 
    _table: JByteArray<'local>, 
    key: JByteArray<'local>, 
    values: JByteArray<'local>
) {
    // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
    // (otherwise it will be dropped too early)
    let raw_kv_pointer = kv_pointer as *mut YcsbKV;
    let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

    let key_len: usize = env.get_array_length(&key).unwrap().try_into().unwrap();
    let value_len: usize = env.get_array_length(&values).unwrap().try_into().unwrap();
    if key_len > MAX_KEY_LEN {
        let err_str = format!("Error: key too long (length {:?}, max {:?})", key_len, MAX_KEY_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    } 
    if value_len > MAX_ITEM_LEN {
        let err_str = format!("Error: value too long (length {:?}, max {:?})", value_len, MAX_ITEM_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    }

    let ycsb_key = YcsbKey::new(&env, key);
    let ycsb_item = YcsbItem::new(&env, values);

    let ret = kv.kv.update_item(&ycsb_key, &ycsb_item);
    match ret {
        Ok(_) => {}
        Err(e) => {
            let err_str = format!("Error updating item: {:?}", e);
            println!("{}", err_str);
            env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        }
    }
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvCommit<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>, 
    kv_pointer: jlong, 
) {
    // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
    // (otherwise it will be dropped too early)
    let raw_kv_pointer = kv_pointer as *mut YcsbKV;
    let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

    let ret = kv.kv.commit();
    match ret {
        Ok(_) => {}
        Err(e) => {
            let err_str = format!("Error committing transaction: {:?}", e);
            println!("{}", err_str);
            env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        }
    }
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

#[repr(C)]
#[derive(PmCopy, Copy, Debug, Hash)]
struct YcsbKey {
    key: [i8; MAX_KEY_LEN],
}

impl YcsbKey {
    fn new<'local>(env: &JNIEnv<'local>, bytes: JByteArray<'local>) -> Self 
    {
        let mut key = [0i8; MAX_KEY_LEN];
        let key_length: usize = env.get_array_length(&bytes).unwrap().try_into().unwrap();
        let key_slice = &mut key[0..key_length];
        env.get_byte_array_region(bytes, 0, key_slice).unwrap();
        Self { key }
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct YcsbItem {
    item: [i8; MAX_ITEM_LEN]
}

impl YcsbItem {
    fn new<'local>(env: &JNIEnv<'local>, bytes: JByteArray<'local>) -> Self 
    {
        let mut item = [0i8; MAX_ITEM_LEN];
        let item_length: usize = env.get_array_length(&bytes).unwrap().try_into().unwrap();
        let item_slice = &mut item[0..item_length];
        env.get_byte_array_region(bytes, 0, item_slice).unwrap();
        Self { item }
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct TestListElement {
    val: u64,
}

fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
