use jni::JNIEnv;
use jni::objects::{JClass, JString, JByteArray};
use jni::sys::jlong;
use jni::strings::JavaStr;

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

const MAX_KEY_LEN: usize = 1024;
const MAX_ITEM_LEN: usize = 1140; 
const REGION_SIZE: u64 = 1024*1024*1024*10; // 20GB
const NUM_KEYS: u64 = 500001; 

// use a constant log id so we don't run into issues trying to restore a KV
const KVSTORE_ID: u128 = 500;

struct YcsbKV {
    kv: KvStore::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>,
    kvstore_id: u128,
}

fn read_filenames(config_path: &str) -> (String, String, String, String) {
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


pub fn main() {
    let (log_file_name, metadata_file_name, list_file_name, item_table_file_name) = read_filenames("config.toml");
    let node_size = 16;

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

    println!("Setting up KV with {:?} keys, {:?}B nodes, {:?} byte regions", NUM_KEYS, node_size, REGION_SIZE);
    KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::setup(
        &mut metadata_region, &mut item_table_region, &mut list_region, &mut log_region, KVSTORE_ID, NUM_KEYS, node_size).unwrap();
    println!("Done setting up! You can now run YCSB workloads");
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvInit<'local>(
        mut env: JNIEnv<'local>,
        _class: JClass<'local>,
        config_file: JString<'local>
    ) -> jlong 
{
    let config_file_name: String = env.get_string(&config_file).unwrap().into();
    let (log_file_name, metadata_file_name, list_file_name, item_table_file_name) = read_filenames(&config_file_name);

    let node_size = 16;

    // Create a file, and a PM region, for each component
    let log_region = open_pm_region(&log_file_name, REGION_SIZE);
    let metadata_region = open_pm_region(&metadata_file_name, REGION_SIZE);
    let item_table_region = open_pm_region(&item_table_file_name, REGION_SIZE);
    let list_region = open_pm_region(&list_file_name, REGION_SIZE);

    let kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::start(
        metadata_region, item_table_region, list_region, log_region, KVSTORE_ID, NUM_KEYS, node_size).unwrap();

    let ret = Box::new(YcsbKV {
        kv,
        kvstore_id: KVSTORE_ID
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

    let ret = kv.kv.create(&ycsb_key, &ycsb_item, kv.kvstore_id);
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

    let ret = kv.kv.update_item(&ycsb_key, &ycsb_item, kv.kvstore_id);
    match ret {
        Ok(_) => {}
        Err(e) => {
            let err_str = format!("Error updating item: {:?}", e);
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
#[derive(PmSafe, PmSized, Copy, Clone, Debug, Hash, PartialEq, Eq)]
struct YcsbKey {
    key: [i8; MAX_KEY_LEN],
}
impl PmCopy for YcsbKey {}

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
#[derive(PmSafe, PmSized, Copy, Clone, Debug, PartialEq, Eq)]
struct YcsbItem {
    item: [i8; MAX_ITEM_LEN]
}
impl PmCopy for YcsbItem {}

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
#[derive(PmSafe, PmSized, Copy, Clone, Debug)]
struct TestListElement {
    val: u64,
}
impl PmCopy for TestListElement {}

fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
