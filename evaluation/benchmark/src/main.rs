// use storage_node::kv::kvimpl_t::*;
// use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use redis::{FromRedisValue, RedisResult};

use std::fs;
use std::env;
use std::time::Instant;
use std::io::{BufWriter, Write};

use rand::thread_rng;
use rand::seq::SliceRandom;

use crate::redis_client::*;
use crate::kv_interface::*;

pub mod kv_interface;
pub mod redis_client;

// length of key and value in byte
const KEY_LEN: usize = 8;
const VALUE_LEN: usize = 8;

const PM_DEV: &str = "/dev/pmem0";
const MOUNT_POINT: &str = "/mnt/pmem";

// TODO: read these from a config file?
const NUM_KEYS: u64 = 5000;
const ITERATIONS: u64 = 10;


#[repr(C)]
#[derive(PmCopy, Copy, Hash)]
struct TestKey {
    key: [u8; KEY_LEN]
}

impl Key for TestKey {
    fn key_str(&self) -> &str {
        std::str::from_utf8(&self.key).unwrap()
    }
}

#[repr(C)]
#[derive(PmCopy, Copy, Hash, Debug)]
struct TestValue {
    value: [u8; VALUE_LEN]
}

impl Value for TestValue {
    fn field_str(&self) -> &str {
        "value"
    }

    fn value_str(&self) -> &str {
        std::str::from_utf8(&self.value).unwrap()
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let output_dir = if args.len() > 1 {
        args[1].clone()
    } else {
        panic!("Please provide output dir path");
    };

    // create per-KV output directories
    let redis_output_dir = output_dir.clone() + "/" + &RedisClient::<TestKey,TestValue>::db_name();
    fs::create_dir_all(&redis_output_dir).unwrap();

    for i in 1..ITERATIONS+1 {
        {
            let mut redis_client = RedisClient::<TestKey, TestValue>::init().unwrap();
            run_sequential_put(&mut redis_client, &redis_output_dir, i).unwrap();
            run_sequential_get(&mut redis_client, &redis_output_dir, i).unwrap();
            run_sequential_update(&mut redis_client, &redis_output_dir, i).unwrap();
            run_sequential_delete(&mut redis_client, &redis_output_dir, i).unwrap();
        }
        
        {
            let mut redis_client = RedisClient::<TestKey, TestValue>::init().unwrap();
            run_rand_put(&mut redis_client, &redis_output_dir, i).unwrap();
            run_rand_get(&mut redis_client, &redis_output_dir, i).unwrap();
            run_rand_update(&mut redis_client, &redis_output_dir, i).unwrap();
            run_rand_delete(&mut redis_client, &redis_output_dir, i).unwrap();
        }
    }
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

// fn open_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
// {
//     #[cfg(target_os = "windows")]
//     let pm_region = FileBackedPersistentMemoryRegion::restore(
//         &file_name, 
//         MemoryMappedFileMediaType::SSD,
//         region_size,
//     ).unwrap();
//     #[cfg(target_os = "linux")]
//     let pm_region = FileBackedPersistentMemoryRegion::restore(
//         &file_name, 
//         region_size
//     ).unwrap();

//     pm_region
// }


// fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion
// {
//     #[cfg(target_os = "windows")]
//     let pm_region = FileBackedPersistentMemoryRegion::new(
//         &file_name, MemoryMappedFileMediaType::SSD,
//         region_size,
//         FileCloseBehavior::TestingSoDeleteOnClose
//     ).unwrap();
//     #[cfg(target_os = "linux")]
//     let pm_region = FileBackedPersistentMemoryRegion::new(
//         &file_name,
//         region_size,
//         PersistentMemoryCheck::DontCheckForPersistentMemory,
//     ).unwrap();

//     pm_region
// }


fn remove_file(name: &str) {
    let _ = std::fs::remove_file(name);
}
