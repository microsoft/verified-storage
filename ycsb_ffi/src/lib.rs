use jni::JNIEnv;
use jni::objects::{JClass, JByteArray};
use jni::sys::{jlong, jint};

use storage_node::kv::kvimpl_t::*;
use storage_node::kv::volatile::volatileimpl_v::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::log::logimpl_t::generate_fresh_log_id;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::{PmSized, PmSafe};
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

const MAX_KEY_LEN: usize = 1024;
const MAX_ITEM_LEN: usize = 1140;

struct YcsbKV {
    kv: KvStore::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>,
    kvstore_id: u128,
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvInit<'local>(_env: JNIEnv<'local>,
        _class: JClass<'local>) -> jlong {

    // TODO: these should be parameters in a config file or something
    let region_size = 2*1024*1024;
    let log_file_name = "/home/hayley/kv_files/test_log";
    let metadata_file_name = "/home/hayley/kv_files/test_metadata";
    let item_table_file_name = "/home/hayley/kv_files/test_item";
    let list_file_name = "/home/hayley/kv_files/test_list";

    let num_keys = 1000;
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

    KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::setup(
        &mut metadata_region, &mut item_table_region, &mut list_region, &mut log_region, kvstore_id, num_keys, node_size).unwrap();

    let kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement, VolatileKvIndexImpl<YcsbKey>>::start(
        metadata_region, item_table_region, list_region, log_region, kvstore_id, num_keys, node_size).unwrap();

    let ret = Box::new(YcsbKV {
        kv,
        kvstore_id
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
    env: JNIEnv<'local>,
    _class: JClass<'local>, 
    kv_pointer: jlong, 
    _table: JByteArray<'local>, 
    key: JByteArray<'local>, 
    values: JByteArray<'local>
) -> jint {
    // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
    // (otherwise it will be dropped too early)
    let raw_kv_pointer = kv_pointer as *mut YcsbKV;
    let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

    let key_len: usize = env.get_array_length(&key).unwrap().try_into().unwrap();
    let value_len: usize = env.get_array_length(&values).unwrap().try_into().unwrap();
    if key_len > MAX_KEY_LEN {
        println!("Error: key too long (length {:?}, max {:?})", key_len, MAX_KEY_LEN);
        return -1;
    } 
    if value_len > MAX_ITEM_LEN {
        println!("Error: value too long (length {:?}, max {:?})", value_len, MAX_ITEM_LEN);
        return -1;
    }

    let ycsb_key = YcsbKey::new(&env, key);
    let ycsb_item = YcsbItem::new(&env, values);

    let ret = kv.kv.create(&ycsb_key, &ycsb_item, kv.kvstore_id);
    match ret {
        Ok(_) => {
            return 0;
        }
        Err(_) => {
            return -1;
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
