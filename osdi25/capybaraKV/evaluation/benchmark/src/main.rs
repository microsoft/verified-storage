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

use pmcopy::PmCopy;
use std::thread::sleep;
use std::time::Duration;
use capybarakv::kv2::spec_t::*;
use capybarakv::pmem::pmcopy_t::*;
use capybarakv::pmem::traits_t::{ConstPmSized, PmSafe, PmSized, UnsafeSpecPmSized};

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use redis::{FromRedisValue, RedisResult};

use std::env;
use std::fs;
use std::time::Instant;
// use std::thread::sleep;
use std::io::{BufWriter, Write};
use std::process::Command;

use rand::seq::SliceRandom;
use rand::thread_rng;

use serde::Deserialize;

use nix::sys;

use crate::kv_interface::*;
use crate::redis_client::*;
use crate::rocksdb_client::*;
use crate::sharded_capybarakv_client::*;
use crate::viper_client::*;

pub mod kv_interface;
pub mod redis_client;
pub mod rocksdb_client;
// pub mod capybarakv_client;
pub mod sharded_capybarakv_client;
pub mod viper_client;
// pub mod custom_bindings;

// length of key and value in byte for most tests
const KEY_LEN: usize = 64;
const VALUE_LEN: usize = 1024;
const LIST_ELEM_LEN: usize = 8;

// large enough to fill up a KV store reasonably quickly, small enough
// to not overflow the stack when statically allocating keys and values.
const BIG_KEY_LEN: usize = 1024;
const BIG_VALUE_LEN: usize = 1024 * 512;

// const PM_DEV: &str = "/dev/pmem0";
// const MOUNT_POINT: &str = "/mnt/pmem";

// #[cfg(feature="mini")]
// const NUM_KEYS: u64 = 25000;
// #[cfg(feature="mini")]
// const LIST_LEN: u64 = 10;
// #[cfg(not(feature="mini"))]
// const NUM_KEYS: u64 = 25000000;
// #[cfg(not(feature="mini"))]
// const LIST_LEN: u64 = 100;
// const ITERATIONS: u64 = 1;
// const START_ITERATIONS: u64 = 5;
// // for use in the full startup experiment
// // 1024*1024*1024*115 / (1024 + 1024*512 + 128) (approximately)
// // 115GB CapybaraKV instances uses 100% of PM device
// // the extra 128 bytes accounts for metadata and CRCs
// const CAPYBARAKV_MAX_KEYS: u64 = 235000;

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct TestKey {
    key: [u8; KEY_LEN],
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct BigTestKey {
    key: [u8; BIG_KEY_LEN],
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
    value: [u8; VALUE_LEN],
}

impl Default for TestValue {
    fn default() -> Self {
        Self {
            value: [0; VALUE_LEN],
        }
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct BigTestValue {
    value: [u8; BIG_VALUE_LEN],
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
        let mut value = TestValue {
            value: [0u8; VALUE_LEN],
        };
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
        let mut value = BigTestValue {
            value: [0u8; BIG_VALUE_LEN],
        };
        value.value[0..v.len()].copy_from_slice(&v);
        value
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Debug)]
pub struct TestListElem {
    val: [u8; LIST_ELEM_LEN],
}

impl ListElement for TestListElem {
    fn element_str(&self) -> &str {
        std::str::from_utf8(&self.val).unwrap()
    }
}

// This has to be implemented, but we're going to ignore it,
// so it doesn't really matter what these return
impl LogicalRange for TestListElem {
    fn start(&self) -> usize {
        // self.val as usize
        0
    }

    fn end(&self) -> usize {
        // self.val as usize
        0
    }
}

impl FromRedisValue for TestValue {
    fn from_redis_value(v: &redis::Value) -> RedisResult<Self> {
        use redis::Value::*;

        // TODO: better error handling for unexpected value types
        let mut out_value = Self {
            value: [0u8; VALUE_LEN],
        };
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
        let mut out_value = Self {
            value: [0u8; BIG_VALUE_LEN],
        };
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

impl FromRedisValue for TestListElem {
    fn from_redis_value(v: &redis::Value) -> RedisResult<Self> {
        use redis::Value::*;

        // TODO: better error handling for unexpected value types
        let mut out_value = Self {
            val: [0u8; LIST_ELEM_LEN],
        };
        if let Array(array) = v {
            if array.len() > 2 {
                panic!("Invalid list element structure");
            }
            // NOTE: The structure of the values here is hardcoded
            // if you change it, this will also have to change!
            let value = &array[1];
            if let BulkString(s) = value {
                if s.len() > LIST_ELEM_LEN {
                    panic!("List element too long");
                }
                out_value.val[..s.len()].copy_from_slice(s);
            } else {
                panic!("Invalid redis list element");
            }
        }
        Ok(out_value)
    }
}

#[derive(Deserialize, Debug)]
struct Config {
    microbenchmark_config: MicrobenchmarkConfig,
}

#[derive(Deserialize, Debug)]
pub struct MicrobenchmarkConfig {
    kv_file: String,
    pm_dev: String,
    mount_point: String,
    results_dir: String,
    experiment_keys: u64,
    per_record_list_len: u64,
    op_iterations: u64,
    start_iterations: u64,
    capybarakv_region_size: u64,
    viper_region_size: u64,
    max_keys: u64,
    run_full_setup: bool,
    max_operations_per_transaction: u64,
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let config_file = if args.len() > 1 {
        args[1].clone()
    } else {
        panic!("Please provide config file")
    };

    let config_contents_str = match fs::read_to_string(&config_file) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Could not read file `{}`: {}", config_file, e);
            panic!();
        }
    };
    let config_contents: Config = toml::from_str(&config_contents_str).unwrap();
    let config = config_contents.microbenchmark_config;
    let output_dir = &config.results_dir;

    // create per-KV output directories
    let redis_output_dir =
        output_dir.clone() + "/" + &RedisClient::<TestKey, TestValue, TestListElem>::db_name();
    let rocksdb_output_dir =
        output_dir.clone() + "/" + &RocksDbClient::<TestKey, TestValue>::db_name();
    let capybara_output_dir = output_dir.clone()
        + "/"
        + &ShardedCapybaraKvClient::<TestKey, TestValue, TestListElem>::db_name();
    let viper_output_dir = output_dir.clone() + "/" + &ViperClient::db_name();

    fs::create_dir_all(&redis_output_dir).unwrap();
    fs::create_dir_all(&rocksdb_output_dir).unwrap();
    fs::create_dir_all(&capybara_output_dir).unwrap();
    fs::create_dir_all(&viper_output_dir).unwrap();

    for i in 1..config.op_iterations + 1 {
        run_experiments::<RedisClient<TestKey, TestValue, TestListElem>>(
            &config,
            &redis_output_dir,
            i,
        )
        .unwrap();
        run_experiments::<RocksDbClient<TestKey, TestValue>>(&config, &rocksdb_output_dir, i)
            .unwrap();
        run_experiments::<ShardedCapybaraKvClient<TestKey, TestValue, TestListElem>>(
            &config,
            &capybara_output_dir,
            i,
        )
        .unwrap();
        run_experiments::<ViperClient>(&config, &viper_output_dir, i).unwrap();
    }

    for i in 1..config.op_iterations + 1 {
        run_list_experiments::<ShardedCapybaraKvClient<TestKey, TestValue, TestListElem>>(
            &config,
            &capybara_output_dir,
            i,
        )
        .unwrap();
        run_list_experiments::<RedisClient<TestKey, TestValue, TestListElem>>(
            &config,
            &redis_output_dir,
            i,
        )
        .unwrap();
    }

    if config.run_full_setup {
        // full setup works differently so that we don't have to rebuild the full KV every iteration
        
        // full setup doesn't work for redis
        // run_full_setup::<RedisClient<TestKey, TestValue, TestListElem>>(&config, &redis_output_dir)
        //     .unwrap();
        
        run_full_setup::<RocksDbClient<TestKey, TestValue>>(&config, &rocksdb_output_dir).unwrap();
        run_full_setup::<ShardedCapybaraKvClient<TestKey, TestValue, TestListElem>>(
            &config,
            &capybara_output_dir,
        )
        .unwrap();
        run_full_setup::<ViperClient>(&config, &viper_output_dir).unwrap();
    }
}

fn run_experiments<KV>(config: &MicrobenchmarkConfig, output_dir: &str, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let mount_point = &config.mount_point;
    let pm_dev = &config.pm_dev;
    let num_keys = config.experiment_keys;
    let max_keys = config.max_keys;

    // sequential access operations
    {
        KV::setup(config)?;
        let mut client = KV::start(config)?;
        run_sequential_put(&mut client, &output_dir, num_keys, i)?;
        client.flush();
        run_sequential_get(&mut client, &output_dir, num_keys, i)?;
        run_sequential_update(&mut client, &output_dir, num_keys, i)?;
        run_sequential_delete(&mut client, &output_dir, num_keys, i)?;
    }
    KV::cleanup(&mount_point, &pm_dev);

    println!("sequential done");

    // random access operations
    {
        KV::setup(config)?;
        let mut client = KV::start(config)?;
        run_rand_put(&mut client, &output_dir, num_keys, i)?;
        client.flush();
        run_rand_get(&mut client, &output_dir, num_keys, i)?;
        run_rand_update(&mut client, &output_dir, num_keys, i)?;
        run_rand_delete(&mut client, &output_dir, num_keys, i)?;
    }
    KV::cleanup(&mount_point, &pm_dev);

    {
        // startup measurements
        for j in 1..config.start_iterations+1 {
            {
                run_empty_start::<KV>(config, &output_dir, j)?;
            }
        }
    }

    Ok(())
}

fn run_list_experiments<KV>(
    config: &MicrobenchmarkConfig,
    output_dir: &str,
    i: u64,
) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue> + ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let mount_point = &config.mount_point;
    let pm_dev = &config.pm_dev;
    let num_keys = config.experiment_keys;
    // {
    //     KV::setup(config)?;
    //     let mut client = KV::start(config)?;
    //     if KV::db_name() == "capybarakv" {
    //         // redis does not the keys to be pre-inserted
    //         insert_keys_for_list_ops(&mut client, num_keys)?;
    //     }
    //     run_sequential_list_append(&mut client, output_dir, config, i)?;
    //     run_sequential_list_read(&mut client, output_dir, config, i)?;
    //     run_sequential_list_get_length(&mut client, output_dir, config, i)?;
    //     run_sequential_list_trim(&mut client, output_dir, config, i)?;
    // }
    // KV::cleanup(&mount_point, &pm_dev);

    {
        KV::setup(config)?;
        let mut client = KV::start(config)?;
        if KV::db_name() == "capybarakv" {
            // redis does not the keys to be pre-inserted
            insert_keys_for_list_ops(&mut client, num_keys)?;
        }
        run_rand_list_append(&mut client, output_dir, config, i)?;
        run_rand_list_read(&mut client, output_dir, config, i)?;
        run_rand_list_get_length(&mut client, output_dir, config, i)?;
        run_rand_list_trim(&mut client, output_dir, config, i)?;
    }
    KV::cleanup(&mount_point, &pm_dev);

    Ok(())
}

fn create_file_and_build_output_stream(output_file: &str) -> BufWriter<fs::File> {
    remove_file(&output_file);
    let f = fs::File::create(&output_file).unwrap();
    let out_stream = BufWriter::new(f);
    out_stream
}

fn u64_to_test_key(i: u64) -> TestKey {
    let mut key = TestKey {
        key: [0u8; KEY_LEN],
    };
    let i_str = i.to_string();
    if i_str.len() > KEY_LEN {
        panic!(
            "key len {:?} is greater than maximum len {:?}",
            i_str.len(),
            KEY_LEN
        );
    }
    let byte_vec: Vec<u8> = i_str.into_bytes();
    key.key[..byte_vec.len()].copy_from_slice(&byte_vec);

    key
}

fn u64_to_big_test_key(i: u64) -> BigTestKey {
    let mut key = BigTestKey {
        key: [0u8; BIG_KEY_LEN],
    };
    let i_str = i.to_string();
    if i_str.len() > BIG_KEY_LEN {
        panic!(
            "key len {:?} is greater than maximum len {:?}",
            i_str.len(),
            BIG_KEY_LEN
        );
    }
    let byte_vec: Vec<u8> = i_str.into_bytes();
    key.key[..byte_vec.len()].copy_from_slice(&byte_vec);

    key
}

// TODO: actually take generics key and value here?
// TODO: more useful error code
fn run_sequential_put<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_put/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL PUT");
    let value = TestValue {
        value: [0u8; VALUE_LEN],
    };
    for i in 0..num_keys {
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

// This function is the same as run_sequential_put but it doesn't time the operations
fn insert_keys_for_list_ops<KV>(kv: &mut KV, num_keys: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue> + ListKvInterface<TestKey, TestValue, TestListElem>,
{
    println!("Filling KV store for list ops");
    let value = TestValue {
        value: [0u8; VALUE_LEN],
    };
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        if let Err(e) = kv.put(&key, &value) {
            return Err(e);
        }
    }
    println!("Done filling KV store");

    Ok(())
}

fn run_sequential_get<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_get/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL GET");
    for i in 0..num_keys {
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

fn run_sequential_update<KV>(
    kv: &mut KV,
    output_dir: &str,
    num_keys: u64,
    i: u64,
) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_update/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL UPDATE");
    let value = TestValue {
        value: [1u8; VALUE_LEN],
    };

    for i in 0..num_keys {
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

fn run_sequential_delete<KV>(
    kv: &mut KV,
    output_dir: &str,
    num_keys: u64,
    i: u64,
) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/sequential_delete/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL DELETE");
    for i in 0..num_keys {
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

fn run_rand_put<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_put/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue {
        value: [0u8; VALUE_LEN],
    };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
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

fn run_rand_get<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_get/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue {
        value: [0u8; VALUE_LEN],
    };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
    key_vec.shuffle(&mut thread_rng());

    println!("RAND GET");
    for i in 0..num_keys {
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

fn run_rand_update<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_update/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue {
        value: [1u8; VALUE_LEN],
    };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
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

fn run_rand_delete<KV>(kv: &mut KV, output_dir: &str, num_keys: u64, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let exp_output_dir = output_dir.to_owned() + "/rand_delete/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue {
        value: [1u8; VALUE_LEN],
    };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
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
fn run_rand_latest_access_pattern<KV>(
    kv: &mut KV,
    output_dir: &str,
    num_keys: u64,
    i: u64,
) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    // let exp_output_dir = output_dir.to_owned() + "/access_latest/";
    // let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    // fs::create_dir_all(&exp_output_dir).unwrap();
    // let mut out_stream = create_file_and_build_output_stream(&output_file);

    let value = TestValue {
        value: [1u8; VALUE_LEN],
    };

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
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

// This function assumes that the keys have already been inserted by
// insert_keys_for_list_ops
fn run_sequential_list_append<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let list_len = config.per_record_list_len;

    let exp_output_dir = output_dir.to_owned() + "/sequential_list_append/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let list_elem = TestListElem {
        val: [1u8; LIST_ELEM_LEN],
    };
    println!("SEQUENTIAL LIST APPEND");
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        for j in 0..list_len {
            let t0 = Instant::now();
            if let Err(e) = kv.append_to_list(&key, list_elem) {
                return Err(e);
            }
            let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
            out_stream.write(&elapsed.into_bytes()).unwrap();
        }
    }
    println!("SEQUENTIAL LIST APPEND DONE");

    Ok(())
}

fn run_sequential_list_read<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let exp_output_dir = output_dir.to_owned() + "/sequential_list_read/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL LIST READ");
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.read_full_list(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("SEQUENTIAL LIST READ DONE");

    Ok(())
}

fn run_sequential_list_get_length<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let exp_output_dir = output_dir.to_owned() + "/sequential_list_len/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL LIST LEN");
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.get_list_length(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("SEQUENTIAL LIST LEN DONE");

    Ok(())
}

fn run_sequential_list_trim<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let list_len = config.per_record_list_len;

    let exp_output_dir = output_dir.to_owned() + "/sequential_list_trim/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("SEQUENTIAL LIST TRIM");
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.trim_list(&key, list_len.try_into().unwrap()) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("SEQUENTIAL LIST TRIM DONE");

    Ok(())
}

// This function assumes that the keys have already been inserted by
// insert_keys_for_list_ops
fn run_rand_list_append<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let list_len = config.per_record_list_len;

    let exp_output_dir = output_dir.to_owned() + "/rand_list_append/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    let mut key_vec = Vec::new();
    for i in 0..num_keys {
        key_vec.append(&mut vec![i; list_len.try_into().unwrap()]);
    }
    key_vec.shuffle(&mut thread_rng());

    let list_elem = TestListElem {
        val: [1u8; LIST_ELEM_LEN],
    };
    println!("RANDOM LIST APPEND");
    for i in 0..num_keys {
        let key = u64_to_test_key(i);

        for j in 0..list_len {
            let t0 = Instant::now();
            if let Err(e) = kv.append_to_list(&key, list_elem) {
                return Err(e);
            }
            let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
            out_stream.write(&elapsed.into_bytes()).unwrap();
        }
    }
    println!("RANDOM LIST APPEND DONE");

    Ok(())
}

fn run_rand_list_read<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;

    let exp_output_dir = output_dir.to_owned() + "/rand_list_read/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
    key_vec.shuffle(&mut thread_rng());

    println!("RANDOM LIST READ");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.read_full_list(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("RANDOM LIST READ DONE");

    Ok(())
}

fn run_rand_list_get_length<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;

    let exp_output_dir = output_dir.to_owned() + "/rand_list_len/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
    key_vec.shuffle(&mut thread_rng());

    println!("RANDOM LIST LEN");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.get_list_length(&key) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("RANDOM LIST LEN DONE");

    Ok(())
}

fn run_rand_list_trim<KV>(
    kv: &mut KV,
    output_dir: &str,
    config: &MicrobenchmarkConfig,
    i: u64,
) -> Result<(), KV::E>
where
    KV: ListKvInterface<TestKey, TestValue, TestListElem>,
{
    let num_keys = config.experiment_keys;
    let list_len = config.per_record_list_len;

    let exp_output_dir = output_dir.to_owned() + "/rand_list_trim/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    // randomize key order
    let mut key_vec = Vec::from_iter(0..num_keys);
    key_vec.shuffle(&mut thread_rng());

    println!("RANDOM LIST TRIM");
    for i in key_vec {
        let key = u64_to_test_key(i);

        let t0 = Instant::now();
        if let Err(e) = kv.trim_list(&key, list_len.try_into().unwrap()) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    println!("RANDOM LIST TRIM DONE");

    Ok(())
}

fn run_empty_start<KV>(config: &MicrobenchmarkConfig, output_dir: &str, i: u64) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
{
    let mount_point = &config.mount_point;
    let pm_dev = &config.pm_dev;
    let num_keys = config.max_keys;

    let exp_output_dir = output_dir.to_owned() + "/empty_setup/";
    let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
    fs::create_dir_all(&exp_output_dir).unwrap();
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("EMPTY SETUP");
    KV::setup(config)?;
    {
        let (_kv, dur) = KV::timed_start(config)?;
        let elapsed = format!("{:?}\n", dur.as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
        out_stream.flush().unwrap();
        println!("EMPTY SETUP DONE");
    }
    KV::cleanup(&mount_point, &pm_dev);

    Ok(())
}

fn run_full_setup<KV>(config: &MicrobenchmarkConfig, output_dir: &str) -> Result<(), KV::E>
where
    KV: KvInterface<TestKey, TestValue>,
    KV::E: std::fmt::Debug,
{
    let mount_point = &config.mount_point;
    let pm_dev = &config.pm_dev;
    let num_keys = config.max_keys;
    let exp_output_dir = output_dir.to_owned() + "/full_setup/";

    println!("FULL SETUP");

    {
        KV::setup(config)?;
        let mut kv = KV::start(config)?;

        // let value = BigTestValue { value: [0u8; BIG_VALUE_LEN] };
        let value = TestValue {
            value: [0u8; VALUE_LEN],
        };
        let mut i = 0;

        println!("Inserting keys until failure");

        // insert keys until the KV store runs out of space
        let mut insert_ok = Ok(());
        while insert_ok.is_ok() {
            let key = u64_to_test_key(i);
            insert_ok = kv.put(&key, &value);
            i += 1;
            if i % 1000000 == 0 {
                println!("Inserted {:?} keys", i);
                // viper throws an exception in a different thread when it runs out space,
                // which we can't really handle from Rust, so instead of waiting for
                // and error we'll periodically check if we're close to running out
                // of space and break when we are
                if KV::db_name() == "viper" {
                    let mount_point_path = std::path::Path::new(mount_point);
                    let stat = sys::statvfs::statvfs(mount_point_path).unwrap();
                    // blocks_available is given in 1K blocks and viper allocates
                    // in 1G files, so stop when there is less than 1G available
                    if stat.blocks_available() < 1048576 {
                        println!("Full, stopping.");
                        break;
                    }
                }
            }
        }
        println!("Maxed out at {:?} keys", i);
    }
    KV::cleanup(&mount_point, &pm_dev);

    println!("Done setting up, running timed start");

    for i in 0..config.start_iterations {
        let output_file = exp_output_dir.to_owned() + "Run" + &i.to_string();
        fs::create_dir_all(&exp_output_dir).unwrap();
        let mut out_stream = create_file_and_build_output_stream(&output_file);
        let (_kv, dur) = KV::timed_start(config)?;
        let elapsed = format!("{:?}\n", dur.as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
        out_stream.flush().unwrap();
    }

    println!("FULL SETUP DONE");
    Ok(())
}

pub fn init_and_mount_pm_fs(mount_point: &str, pm_dev: &str) {
    println!("Mounting PM FS...");

    unmount_pm_fs(pm_dev);

    println!("Unmounted");

    // Set up PM with a fresh file system instance
    Command::new("sudo")
        .args(["mkfs.ext4", pm_dev, "-F"])
        .status()
        .expect("mkfs.ext4 failed");

    Command::new("sudo")
        .args(["mount", "-o", "dax", pm_dev, mount_point])
        .status()
        .expect("mount failed");

    Command::new("sudo")
        .args(["chmod", "777", mount_point])
        .status()
        .expect("chmod failed");
    println!("Mounted");
}

pub fn remount_pm_fs(mount_point: &str, pm_dev: &str) {
    println!("Remounting existing FS...");

    unmount_pm_fs(pm_dev);

    println!("Unmounted");

    Command::new("sudo")
        .args(["mount", "-o", "dax", pm_dev, mount_point])
        .status()
        .expect("mount failed");

    println!("Mounted");
}

pub fn unmount_pm_fs(pm_dev: &str) {
    // sleep(Duration::from_secs(5));
    let status = Command::new("sudo").args(["umount", pm_dev, "-f"]).status();
    if let Err(e) = status {
        println!("{:?}", e);
    }
}

fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
