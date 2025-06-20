use jni::JNIEnv;
use jni::objects::{JClass, JByteArray};
use jni::sys::jlong;

use capybarakv::kv2::spec_t::*;
use capybarakv::kv2::shardkv_t::*;
use capybarakv::kv2::shardkv_v::*;
use capybarakv::kv2::concurrentspec_t::*;
#[cfg(target_os = "linux")]
use capybarakv::pmem::linux_pmemfile_t::*;
#[cfg(target_os = "windows")]
use capybarakv::pmem::windows_pmemfile_t::*;
use capybarakv::pmem::pmcopy_t::*;
use capybarakv::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmcopy::PmCopy;
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use serde::Deserialize;
use std::fs;
use std::env;
use std::hash::Hash;
use std::collections::VecDeque;
// use chrono;

const MAX_KEY_LEN: usize = 24; // TODO: check that this is ok
const MAX_ITEM_LEN: usize = 1140; 
const MAX_CONFIG_FILE_NAME_LEN: usize = 1024;

// use a constant log id so we don't run into issues trying to restore a KV
const KVSTORE_ID: u128 = 500;

struct PlaceholderCB {}

verus! {
    impl<K, I, L, Op> MutatingLinearizer<K, I, L, Op> for PlaceholderCB
    where 
        Op: MutatingOperation<K, I, L>,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type Completion = Self;

    closed spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    closed spec fn pre(self, id: int, op: Op) -> bool
    {
        true
    }

    closed spec fn post(
        self,
        complete: Self::Completion,
        id: int,
        op: Op,
        exec_result: Result<Op::KvResult, KvError>,
    ) -> bool
    {
        true
    }

    proof fn apply(
        tracked self,
        op: Op,
        new_ckv: ConcurrentKvStoreView<K, I, L>,
        exec_result: Result<Op::KvResult, KvError>,
        tracked r: &mut GhostVarAuth<ConcurrentKvStoreView<K, I, L>>
    ) -> (tracked complete: Self::Completion)
    {
        admit();
        self
    }
}

impl<K, I, L> ReadLinearizer<K, I, L, ReadItemOp<K>> for PlaceholderCB
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    type Completion = Self;

    open spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    open spec fn pre(self, id: int, op: ReadItemOp<K>) -> bool
    {
        true
    }

    open spec fn post(
        self,
        completion: Self,
        id: int,
        op: ReadItemOp<K>,
        result: Result<I, KvError>,
    ) -> bool
    {
        true
    }

    proof fn apply(
        tracked self,
        op: ReadItemOp<K>,
        result: Result<I, KvError>,
        tracked r: &GhostVarAuth<ConcurrentKvStoreView<K, I, L>>
    ) -> tracked Self::Completion
    {
        
        // r.agree(&self);
        self
    }
}
}

struct YcsbKV {
    kv: ShardedKvStore::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement>,
    _kvstore_id: u128,
}

impl YcsbKV {
    pub fn setup(capybarakv_config: &DbOptions, experiment_config: &ExperimentOptions) {
        // TODO: more explanatory error messages when these fail
        // the KV must have enough space for the number of records used in the experiment
        assert!(capybarakv_config.num_keys >= experiment_config.record_count);
        // sanity check -- we will never want to use more threads than keys
        assert!(capybarakv_config.num_keys >= experiment_config.threads);

        let per_thread_region_size = capybarakv_config.region_size / experiment_config.threads;
        // add one to account for cases where the number of keys is not divisble
        // by the number of threads. this ensures that the remaining keys are 
        // spread out across multiple shards
        let per_thread_num_keys = (capybarakv_config.num_keys / experiment_config.threads) + 1; 

        let setup_parameters = SetupParameters {
            kvstore_id: KVSTORE_ID,
            logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
            max_keys: per_thread_num_keys,
            max_list_elements: 10, // TODO: set this to something that makes sense
            max_operations_per_transaction: 5 // TODO: set this to something that makes sense
        };

        let mut pms = VecDeque::new();

        for i in 0..experiment_config.threads {
            let i: u64 = i.try_into().unwrap();
            let current_file_name = get_kv_file_name(&capybarakv_config.kv_file, i);

            // delete the test files if they already exist. Ignore the result,
            // since it's ok if the files don't exist.
            println!("Setting up with file {:?}", current_file_name);
            remove_file(&current_file_name);

            println!("Setting up KV {:?} with {:?} keys, {:?}B nodes, {:?}B regions", i, per_thread_num_keys, capybarakv_config.node_size, per_thread_region_size);
            let kv_region = create_pm_region(&current_file_name, per_thread_region_size);
            pms.push_back(kv_region);
        }

        let (_ckv, _) = setup::<FileBackedPersistentMemoryRegion, YcsbKey, YcsbItem, TestListElement>(
            pms, &setup_parameters, Ghost::assume_new(), Ghost::assume_new(), Ghost::assume_new()).unwrap();
    }
}


#[derive(Deserialize, Debug)]
struct CapybaraKvConfig {
    capybarakv_config: DbOptions,
}

#[derive(Deserialize, Debug)]
struct ExperimentConfig {
    experiment_config: ExperimentOptions,
}

#[derive(Deserialize, Debug)]
struct DbOptions {
    kv_file: String,
    node_size: u32, 
    num_keys: u64, 
    region_size: u64, 
}

// Most of these options are not used at all in this crate,
// but a few are, and reading from this config file makes it 
// easier to ensure that we use the same configurations everywhere
#[allow(dead_code)]
#[derive(Deserialize, Debug)]
struct ExperimentOptions {
    results_dir: String,
    threads: u64,
    mount_point: String,
    pm_device: String,
    iterations: u64,
    op_count: u64,
    record_count: u64,
}

fn parse_capybarakv_configs(capybarakv_config_file: String) -> DbOptions {
    // println!("{:?}", chrono::offset::Local::now());
    // println!("Reading CapybaraKV configs from {:?}", capybarakv_config_file);
    let capybarakv_config_contents = match fs::read_to_string(&capybarakv_config_file) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Could not read file `{}`: {}", capybarakv_config_file, e);
            panic!();
        }
    };

    // TODO: Proper error handling of invalid config files
    let capybarakv_config: CapybaraKvConfig = toml::from_str(&capybarakv_config_contents).unwrap();
    // println!("capybarakv_config: {:?}", capybarakv_config);
    capybarakv_config.capybarakv_config
}

fn parse_experiment_configs(experiment_config_file: String) -> ExperimentOptions {
    // println!("Reading experiment configs from {:?}", experiment_config_file);
    let experiment_config_contents = match fs::read_to_string(&experiment_config_file) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Could not read file `{}`: {}", experiment_config_file, e);
            panic!();
        }
    };

    let experiment_config: ExperimentConfig = toml::from_str(&experiment_config_contents).unwrap();
    // println!("experiment_config: {:?}", experiment_config);
    experiment_config.experiment_config
}

fn get_kv_file_name(kv_file: &str, id: u64) -> String {
    format!("{}_{}", kv_file, id)
}

pub fn main() {
    let args: Vec<String> = env::args().collect();
    let capybarakv_config_file = if args.len() > 1 {
        args[1].clone()
    } else {
        // "capybarakv_config.toml".to_string()
        panic!("Please provide a path to the CapybaraKV config file");
    };
    let experiment_config_file = if args.len() > 2 {
        args[2].clone()
    } else {
        panic!("Please provide a path to the experiment config file");
    };

    let capybarakv_config = parse_capybarakv_configs(capybarakv_config_file);
    let experiment_config = parse_experiment_configs(experiment_config_file);

    YcsbKV::setup(&capybarakv_config, &experiment_config);


    // // TODO: more explanatory error messages when these fail
    // // the KV must have enough space for the number of records used in the experiment
    // assert!(capybarakv_config.num_keys >= experiment_config.record_count);
    // // sanity check -- we will never want to use more threads than keys
    // assert!(capybarakv_config.num_keys >= experiment_config.threads);

    // let per_thread_region_size = capybarakv_config.region_size / experiment_config.threads;
    // // add one to account for cases where the number of keys is not divisble
    // // by the number of threads. this ensures that the remaining keys are 
    // // spread out across multiple shards
    // let per_thread_num_keys = (capybarakv_config.num_keys / experiment_config.threads) + 1; 

    // let setup_parameters = SetupParameters {
    //     kvstore_id: KVSTORE_ID,
    //     logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
    //     max_keys: per_thread_num_keys,
    //     max_list_elements: 10, // TODO: set this to something that makes sense
    //     max_operations_per_transaction: 5 // TODO: set this to something that makes sense
    // };

    
    // for i in 0..experiment_config.threads {
    //     let i: u64 = i.try_into().unwrap();
    //     let current_file_name = get_kv_file_name(&capybarakv_config.kv_file, i);

    //     // delete the test files if they already exist. Ignore the result,
    //     // since it's ok if the files don't exist.
    //     remove_file(&current_file_name);

    //     println!("Setting up KV {:?} with {:?} keys, {:?}B nodes, {:?}B regions", i, per_thread_num_keys, capybarakv_config.node_size, per_thread_region_size);
    //     // Create a file, and a PM region, for each component
    //     let mut kv_region = create_pm_region(&current_file_name, per_thread_region_size);
    //     KvStore::<_, YcsbKey, YcsbItem, TestListElement>::setup(
    //         &mut kv_region, &setup_parameters).unwrap();

    //     let mut kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement>::start(kv_region, KVSTORE_ID).unwrap();

    //     // Simple read/write/delete test
    //     let test_key = "test_key";
    //     let test_value = "test_value";

    //     let ycsb_key = YcsbKey::new_from_slice(&test_key.as_bytes().iter().map(|&b| b as i8).collect::<Vec<i8>>());
    //     let ycsb_item = YcsbItem::new_from_slice(&test_value.as_bytes().iter().map(|&b| b as i8).collect::<Vec<i8>>());

    //     kv.tentatively_create(&ycsb_key, &ycsb_item).unwrap();

    //     // Read operation
    //     kv.read_item(&ycsb_key).unwrap();

    //     // Delete operation
    //     kv.tentatively_delete(&ycsb_key).unwrap();
    // }    
    println!("Done setting up! You can now run YCSB workloads");
}

fn get_file_name_from_jbytearray<'local>(env: &mut JNIEnv<'local>, jfilename: JByteArray<'local>) -> String {
    let mut file_array = [0i8; MAX_CONFIG_FILE_NAME_LEN];
    let file_name_len: usize = env.get_array_length(&jfilename).unwrap().try_into().unwrap();
    if file_name_len > MAX_CONFIG_FILE_NAME_LEN {
        let err_str = format!("Error: config file path too long (length {:?}, max {:?})", file_name_len, MAX_CONFIG_FILE_NAME_LEN);
        println!("{}", err_str);
        env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        unreachable!();
    }
    let file_name_slice = &mut file_array[0..file_name_len];
    env.get_byte_array_region(jfilename, 0, file_name_slice).unwrap();
    String::from_utf8(file_name_slice.iter().map(|&c| c as u8).collect()).unwrap()
}

#[no_mangle]
pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvInit<'local>(
    mut env: JNIEnv<'local>,
    _class: JClass<'local>,
    capybarakv_config_file: JByteArray<'local>,
    experiment_config_file: JByteArray<'local>,
) -> jlong {
    let capybarakv_config_file_name = get_file_name_from_jbytearray(&mut env, capybarakv_config_file);
    let experiment_config_file_name = get_file_name_from_jbytearray(&mut env, experiment_config_file);
    
    let capybarakv_config = parse_capybarakv_configs(capybarakv_config_file_name);
    let experiment_config = parse_experiment_configs(experiment_config_file_name);

    let per_thread_region_size = capybarakv_config.region_size / experiment_config.threads;

    // open the PM files for each shard
    let mut pms = VecDeque::new();
    for i in 0..experiment_config.threads {
        let i: u64 = i.try_into().unwrap();
        let current_file_name = get_kv_file_name(&capybarakv_config.kv_file, i);
        let kv_region = open_pm_region(&current_file_name, per_thread_region_size);
        pms.push_back(kv_region);
    }

    // let kv = KvStore::<_, YcsbKey, YcsbItem, TestListElement>::start(kv_region, KVSTORE_ID).unwrap();
    let kv = recover(pms, KVSTORE_ID, Ghost::assume_new(), Ghost::assume_new(), Ghost::assume_new(), Ghost::assume_new()).unwrap(); 

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

    let (ret, _) = kv.kv.create(&ycsb_key, &ycsb_item, Tracked::<PlaceholderCB>::assume_new());
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
    let (result, _) = kv.kv.read_item(&ycsb_key, Tracked::<PlaceholderCB>::assume_new());
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

    let (ret, _) = kv.kv.update_item(&ycsb_key, &ycsb_item, Tracked::<PlaceholderCB>::assume_new());
    match ret {
        Ok(_) => {}
        Err(e) => {
            let err_str = format!("Error updating item: {:?}", e);
            println!("{}", err_str);
            env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
        }
    }
}

// #[no_mangle]
// pub extern "system" fn Java_site_ycsb_db_CapybaraKV_kvCommit<'local>(
//     mut env: JNIEnv<'local>,
//     _class: JClass<'local>, 
//     kv_pointer: jlong, 
// ) {
//     // Obtain a reference to the KV. We don't use Box::from_raw because we don't want ownership of the KV
//     // (otherwise it will be dropped too early)
//     let raw_kv_pointer = kv_pointer as *mut YcsbKV;
//     let kv: &mut YcsbKV = unsafe { &mut *raw_kv_pointer };

//     let ret = kv.kv.commit();
//     match ret {
//         Ok(_) => {}
//         Err(e) => {
//             let err_str = format!("Error committing transaction: {:?}", e);
//             println!("{}", err_str);
//             env.throw(("java/site/ycsb/CapybaraKvException", err_str)).unwrap();
//         }
//     }
// }

fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
{
    #[cfg(target_os = "windows")]
    let pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name, 
        MemoryMappedFileMediaType::BatteryBackedDRAM,
        region_size,
        FileCloseBehavior::Persistent
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
        MemoryMappedFileMediaType::BatteryBackedDRAM,
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

    // fn new_from_slice(slice: &[i8]) -> Self {
    //     let mut key = [0i8; MAX_KEY_LEN];
    //     key[0..slice.len()].copy_from_slice(slice);
    //     Self { key }
    // }
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

    // fn new_from_slice(slice: &[i8]) -> Self {
    //     let mut item = [0i8; MAX_ITEM_LEN];
    //     item[0..slice.len()].copy_from_slice(slice);
    //     Self { item }
    // }
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
struct TestListElement {
    val: u64,
}

impl LogicalRange for TestListElement {
    fn start(&self) -> usize {
        self.val as usize
    }

    fn end(&self) -> usize {
        self.val as usize
    }
}

fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}