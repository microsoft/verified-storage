#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(dependency_on_unit_never_type_fallback)]
#![allow(unused_imports)]
#![allow(deprecated)]

// these are required to suppress warnings from bindgen-generated code
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]

include!("./bindings.rs");

// use storage_node::kv::kvimpl_t::*;
// use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::kv2::spec_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use redis::{FromRedisValue, RedisResult};

use std::fs;
use std::env;
use std::time::{Instant};
// use std::thread::sleep;
use std::io::{BufWriter, Write};
use std::process::Command;

use rand::thread_rng;
use rand::seq::SliceRandom;

use crate::kv_interface::*;
use crate::redis_client::*;
use crate::rocksdb_client::*;
use crate::capybarakv_client::*;
use crate::viper_client::*;

pub mod kv_interface;
pub mod redis_client;
pub mod rocksdb_client;
pub mod capybarakv_client;
pub mod viper_client;
// pub mod custom_bindings;

// length of key and value in byte for most tests
const KEY_LEN: usize = 64;
const VALUE_LEN: usize = 1024;

// large enough to fill up a KV store reasonably quickly, small enough
// to not overflow the stack when statically allocating keys and values.
const BIG_KEY_LEN: usize = 1024;
const BIG_VALUE_LEN: usize = 1024 * 512;

const PM_DEV: &str = "/dev/pmem0";
const MOUNT_POINT: &str = "/mnt/pmem";

// TODO: read these from a config file?
// const NUM_KEYS: u64 = 25000000;
const NUM_KEYS: u64 = 1;
const ITERATIONS: u64 = 1;
// for use in the full startup experiment
// 1024*1024*1024*115 / (1024 + 1024*512 + 128) (approximately)
// 115GB CapybaraKV instances uses 100% of PM device
// the extra 128 bytes accounts for metadata and CRCs 
const CAPYBARAKV_MAX_KEYS: u64 = 235000; 


#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct TestKey {
    key: [u8; KEY_LEN]
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct BigTestKey {
    key: [u8; BIG_KEY_LEN]
}

impl Key for TestKey {
    fn key_str(&self) -> &str {
        std::str::from_utf8(&self.key).unwrap()
    }
}

impl Key for BigTestKey {
    fn key_str(&self) -> &str {
        std::str::from_utf8(&self.key).unwrap()
    }
}

impl AsRef<[u8]> for TestKey {
    fn as_ref(&self) -> &[u8] {
        &self.key
    }
}

impl AsRef<[u8]> for BigTestKey {
    fn as_ref(&self) -> &[u8] {
        &self.key
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct TestValue {
    value: [u8; VALUE_LEN]
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct BigTestValue {
    value: [u8; BIG_VALUE_LEN]
}


impl AsRef<[u8]> for TestValue {
    fn as_ref(&self) -> &[u8] {
        &self.value
    }
}

impl AsRef<[u8]> for BigTestValue {
    fn as_ref(&self) -> &[u8] {
        &self.value
    }
}

impl Value for TestValue {
    fn field_str(&self) -> &str {
        "value"
    }

    fn value_str(&self) -> &str {
        std::str::from_utf8(&self.value).unwrap()
    }

    fn from_byte_vec(v: Vec<u8>) -> Self {
        if v.len() > VALUE_LEN {
            panic!("value is too long");
        }
        let mut value = TestValue { value: [0u8; VALUE_LEN] };
        value.value[0..v.len()].copy_from_slice(&v);
        value
    }
}

impl Value for BigTestValue {
    fn field_str(&self) -> &str {
        "value"
    }

    fn value_str(&self) -> &str {
        std::str::from_utf8(&self.value).unwrap()
    }

    fn from_byte_vec(v: Vec<u8>) -> Self {
        if v.len() > BIG_VALUE_LEN {
            panic!("value is too long");
        }
        let mut value = BigTestValue { value: [0u8; BIG_VALUE_LEN] };
        value.value[0..v.len()].copy_from_slice(&v);
        value
    }
}

// CapybaraKv requires a list element type parameter but 
// currently doesn't use it; we still have to define one
// because it has to be PmCopy (so we can't use () or something)
#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
pub struct PlaceholderListElem {
    val: u64,
}

impl LogicalRange for PlaceholderListElem {
    fn start(&self) -> usize {
        self.val as usize
    }

    fn end(&self) -> usize {
        self.val as usize
    }
}

impl FromRedisValue for TestValue {
    fn from_redis_value(v: &redis::Value) -> RedisResult<Self> {
        use redis::Value::*;

        // TODO: better error handling for unexpected value types
        let mut out_value = Self { value: [0u8; VALUE_LEN] };
        if let Array(array) = v {
            if array.len() > 2 {
                panic!("Invalid value structure");
            }
            // NOTE: The structure of the values here is hardcoded
            // if you change it, this will also have to change!
            let value = &array[1];
            if let BulkString(s) = value {
                if s.len() > VALUE_LEN {
                    panic!("Value too long");
                }
                out_value.value[..s.len()].copy_from_slice(s);
            } else {
                panic!("Invalid redis value");
            }
        }
        Ok(out_value)
    }   
}

impl FromRedisValue for BigTestValue {
    fn from_redis_value(v: &redis::Value) -> RedisResult<Self> {
        use redis::Value::*;

        // TODO: better error handling for unexpected value types
        let mut out_value = Self { value: [0u8; BIG_VALUE_LEN] };
        if let Array(array) = v {
            if array.len() > 2 {
                panic!("Invalid value structure");
            }
            // NOTE: The structure of the values here is hardcoded
            // if you change it, this will also have to change!
            let value = &array[1];
            if let BulkString(s) = value {
                if s.len() > BIG_VALUE_LEN {
                    panic!("Value too long");
                }
                out_value.value[..s.len()].copy_from_slice(s);
            } else {
                panic!("Invalid redis value");
            }
        }
        Ok(out_value)
    }
    
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let output_dir = if args.len() > 1 {
        args[1].clone()
    } else {
        panic!("Please provide output dir path");
    };

    // create per-KV output directories
    let redis_output_dir = output_dir.clone() + "/" + &RedisClient::<TestKey,TestValue>::db_name();
    let rocksdb_output_dir = output_dir.clone() + "/" + &RocksDbClient::<TestKey,TestValue>::db_name();
    let capybara_output_dir = output_dir.clone() + "/" + &CapybaraKvClient::<TestKey, TestValue, PlaceholderListElem>::db_name();
    let viper_output_dir = output_dir.clone() + "/" + &ViperClient::db_name();

    fs::create_dir_all(&redis_output_dir).unwrap();
    fs::create_dir_all(&rocksdb_output_dir).unwrap();
    fs::create_dir_all(&capybara_output_dir).unwrap();
    fs::create_dir_all(&viper_output_dir).unwrap();


    for i in 1..ITERATIONS+1 {
        // run_experiments::<RedisClient<TestKey, TestValue>>(&redis_output_dir, i).unwrap();
        // run_experiments::<RocksDbClient<TestKey, TestValue>>(&rocksdb_output_dir, i).unwrap();
        // run_experiments::<CapybaraKvClient<TestKey, TestValue, PlaceholderListElem>>(&capybara_output_dir, i).unwrap();
        run_experiments::<ViperClient>(&viper_output_dir, i).unwrap();
    }

    // // full setup works differently so that we don't have to rebuild the full KV every iteration
    // run_full_setup::<RedisClient<BigTestKey, BigTestValue>>(&redis_output_dir, NUM_KEYS).unwrap();
    // run_full_setup::<RocksDbClient<BigTestKey, BigTestValue>>(&rocksdb_output_dir, NUM_KEYS).unwrap();
    // run_full_setup::<CapybaraKvClient<BigTestKey, BigTestValue, PlaceholderListElem>>(&capybara_output_dir, CAPYBARAKV_MAX_KEYS).unwrap();
}

fn test_setup<KV>(output_dir: &str) -> Result<(), KV::E> 
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let mut client = KV::start()?;

    Ok(())
}

fn run_experiments<KV>(output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    // sequential access operations
    {
        KV::setup(NUM_KEYS)?;
        let mut client = KV::start()?;
        run_sequential_put(&mut client, &output_dir, i)?;
        client.flush();
        // run_sequential_get(&mut client, &output_dir, i)?;
        // run_sequential_update(&mut client, &output_dir, i)?;
        // run_sequential_delete(&mut client, &output_dir, i)?;
    }
    KV::cleanup();

    // random access operations
    {
        KV::setup(NUM_KEYS)?;
        let mut client = KV::start()?;
        run_rand_put(&mut client, &output_dir, i)?;
        client.flush();
        // run_rand_get(&mut client, &output_dir, i)?;
        // run_rand_update(&mut client, &output_dir, i)?;
        // run_rand_delete(&mut client, &output_dir, i)?;
    }
    KV::cleanup();

    // // // mimic run d from YCSB
    // // {
    // //     KV::setup(NUM_KEYS)?;
    // //     let mut client = KV::start()?;
    // //     run_rand_latest_access_pattern(&mut client, &output_dir, i)?;
    // // }
    // // KV::cleanup();

    // // startup measurements
    // {
    //     run_empty_start::<KV>(&output_dir, i, CAPYBARAKV_MAX_KEYS)?;
    // }
    // KV::cleanup();

    Ok(())
}

fn create_file_and_build_output_stream(output_file: &str) -> BufWriter<fs::File>
{
    remove_file(&output_file);
    let f = fs::File::create(&output_file).unwrap();
    let out_stream = BufWriter::new(f);
    out_stream
}

fn u64_to_test_key(i: u64) -> TestKey {
    let mut key = TestKey { key: [0u8; KEY_LEN] };
    let i_str = i.to_string();
    if i_str.len() > KEY_LEN {
        panic!("key len {:?} is greater than maximum len {:?}", i_str.len(), KEY_LEN);
    }
    let byte_vec: Vec<u8> = i_str.into_bytes();
    key.key[..byte_vec.len()].copy_from_slice(&byte_vec);

    key
}

fn u64_to_big_test_key(i: u64) -> BigTestKey {
    let mut key = BigTestKey { key: [0u8; BIG_KEY_LEN] };
    let i_str = i.to_string();
    if i_str.len() > BIG_KEY_LEN {
        panic!("key len {:?} is greater than maximum len {:?}", i_str.len(), BIG_KEY_LEN);
    }
    let byte_vec: Vec<u8> = i_str.into_bytes();
    key.key[..byte_vec.len()].copy_from_slice(&byte_vec);

    key
}


// TODO: actually take generics key and value here?
// TODO: more useful error code
fn run_sequential_put<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_put/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL PUT");
    let value = TestValue { value: [0u8; VALUE_LEN] };
    for i in 0..NUM_KEYS {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.put(&key, &value) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("SEQUENTIAL PUT DONE");

    Ok(())
}

fn run_sequential_get<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_get/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL GET");
    for i in 0..NUM_KEYS {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.get(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("SEQUENTIAL GET DONE");

    Ok(())
}

fn run_sequential_update<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_update/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL UPDATE");
    let value = TestValue { value: [1u8; VALUE_LEN] };
    
    for i in 0..NUM_KEYS {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.update(&key, &value) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("SEQUENTIAL UPDATE DONE");

    Ok(())
}

fn run_sequential_delete<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_delete/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL DELETE");
    for i in 0..NUM_KEYS {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.delete(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("SEQUENTIAL DELETE DONE");

    Ok(())
}

fn run_rand_put<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_put/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue { value: [0u8; VALUE_LEN] };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..NUM_KEYS);
    key_vec.shuffle(&mut thread_rng());

    println!("RAND PUT");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.put(&key, &value) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("RAND PUT DONE");

    Ok(())
}

fn run_rand_get<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>
{
    let exp_output_dir = output_dir.to_owned() + "/rand_get/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue { value: [0u8; VALUE_LEN] };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..NUM_KEYS);
    key_vec.shuffle(&mut thread_rng());

    println!("RAND GET");
    for i in 0..NUM_KEYS {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.get(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("RAND GET DONE");

    Ok(())
}

fn run_rand_update<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_update/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue { value: [1u8; VALUE_LEN] };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..NUM_KEYS);
    key_vec.shuffle(&mut thread_rng());

    println!("RAND UPDATE");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.update(&key, &value) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("RAND UPDATE DONE");

    Ok(())
}

fn run_rand_delete<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_delete/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue { value: [1u8; VALUE_LEN] };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..NUM_KEYS);
    key_vec.shuffle(&mut thread_rng());

    println!("RAND DELETE");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.delete(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("RAND DELETE DONE");

    Ok(())
}

// this one is currently just for tracing and doesn't record latencies
fn run_rand_latest_access_pattern<KV>(kv: &mut KV, output_dir: &str, i: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    // let exp_output_dir = output_dir.to_owned() + "/access_latest/";
    // let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    // fs::create_dir_all(&exp_output_dir).unwrap();
    // let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue { value: [1u8; VALUE_LEN] };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..NUM_KEYS);
    key_vec.shuffle(&mut thread_rng());

    println!("ACCESS LATEST");
    for i in &key_vec {
        let key = u64_to_test_key(*i);

        kv.put(&key, &value)?;
        kv.get(&key)?;
        kv.get(&key)?;
        kv.get(&key)?;
    }
    println!("ACCESS LATEST DONE");

    Ok(())

}


fn run_empty_start<KV>(output_dir: &str, i: u64, num_keys: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/empty_setup/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("EMPTY SETUP");
    KV::setup(num_keys)?;
    let (_kv, dur) = KV::timed_start()?;
    let elapsed = format!("{:?}\n", dur.as_micros());
    out_stream.write(&elapsed.into_bytes()).unwrap();
    out_stream.flush().unwrap();
    println!("EMPTY SETUP DONE");

    Ok(())
}

fn run_full_setup<KV>(output_dir: &str, num_keys: u64) -> Result<(), KV::E>
    where 
        KV: KvInterface<BigTestKey, BigTestValue>,
        KV::E: std::fmt::Debug,
{
    let exp_output_dir = output_dir.to_owned() + "/full_setup/";
    
    println!("FULL SETUP");

    {
        KV::setup(num_keys)?;
        let mut kv = KV::start()?;
    
        let value = BigTestValue { value: [0u8; BIG_VALUE_LEN] };
        let mut i = 0;

        println!("Inserting keys until failure");
    
        // insert keys until the KV store runs out of space
        let mut insert_ok = Ok(());
        while insert_ok.is_ok() {
            let key = u64_to_big_test_key(i);
            insert_ok = kv.put(&key, &value);
            i += 1;
            if i % 10000 == 0 {
                println!("Inserted {:?} keys", i);
            }
        }
        println!("Maxed out at {:?} keys", i);
    }
    KV::cleanup();

    for i in 0..ITERATIONS {
        let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
        fs::create_dir_all(&exp_output_dir).unwrap();
        let mut out_stream = create_file_and_build_output_stream(&output_file);
        let (_kv, dur) = KV::timed_start()?;
        let elapsed = format!("{:?}\n", dur.as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
        out_stream.flush().unwrap();
    }

    println!("FULL SETUP DONE");
    Ok(())
}

pub fn init_and_mount_pm_fs() {
    println!("Mounting PM FS...");

    unmount_pm_fs();

    println!("Unmounted");

    // Set up PM with a fresh file system instance
    Command::new("sudo")
        .args(["mkfs.ext4", PM_DEV, "-F"])
        .status()
        .expect("mkfs.ext4 failed");

    Command::new("sudo")
        .args(["mount", "-o", "dax", PM_DEV, MOUNT_POINT])
        .status()
        .expect("mount failed");

    Command::new("sudo")
        .args(["chmod", "777", MOUNT_POINT])
        .status()
        .expect("chmod failed");
    println!("Mounted");
}

pub fn remount_pm_fs() {
    println!("Remounting existing FS...");

    unmount_pm_fs();

    println!("Unmounted");

    Command::new("sudo")
        .args(["mount", "-o", "dax", PM_DEV, MOUNT_POINT])
        .status()
        .expect("mount failed");

    println!("Mounted");
}

pub fn unmount_pm_fs() {
    let status = Command::new("sudo")
        .args(["umount", PM_DEV])
        .status();
    if let Err(e) = status {
        println!("{:?}", e);
    }
}


fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
