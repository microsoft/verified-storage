// use storage_node::kv::kvimpl_t::*;
// use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

use std::fs;
use std::env;
use std::time::Instant;
use std::io::{BufWriter, Write};

use crate::redis_client::*;
use crate::kv_interface::*;

pub mod kv_interface;
pub mod redis_client;

// length of key and value in byte
const KEY_LEN: usize = 8;
const VALUE_LEN: usize = 8;

// TODO: read these from a config file?
const NUM_KEYS: u64 = 5000;
// const ITERATIONS: u64 = 100;


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
#[derive(PmCopy, Copy, Hash)]
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let output_dir = if args.len() > 1 {
        args[1].clone()
    } else {
        panic!("Please provide output dir path");
    };

    let mut redis_client = RedisClient::<TestKey, TestValue>::init().unwrap();
    
    // create per-KV output directories
    let redis_output_dir = output_dir.clone() + "/" + &redis_client.db_name();
    fs::create_dir_all(&redis_output_dir).unwrap();

    run_sequential_put(&mut redis_client, &redis_output_dir).unwrap();

}

fn create_file_and_build_output_stream(output_file: &str) -> BufWriter<fs::File>
{
    remove_file(&output_file);
    let f = fs::File::create(&output_file).unwrap();
    let out_stream = BufWriter::new(f);
    out_stream
}

// TODO: actually take generics key and value here?
// TODO: more useful error code
fn run_sequential_put<KV>(kv: &mut KV, output_dir: &str) -> Result<(), KV::E>
    where 
        KV: KvInterface<TestKey, TestValue>,
{
    let output_file = output_dir.to_owned() + "/" + "sequential_put";
    let mut out_stream = create_file_and_build_output_stream(&output_file);

    println!("PUT");
    let value = TestValue { value: [0u8; VALUE_LEN] };
    for i in 0..NUM_KEYS {
        let mut key = TestKey { key: [0u8; KEY_LEN] };
        let i_str = i.to_string();
        if i_str.len() > KEY_LEN {
            panic!("key len {:?} is greater than maximum len {:?}", i_str.len(), KEY_LEN);
        }
        let byte_vec: Vec<u8> = i_str.into_bytes();
        key.key[..byte_vec.len()].copy_from_slice(&byte_vec);

        let t0 = Instant::now();
        if let Err(e) = kv.put(&key, &value) {
            return Err(e);
        }
        let elapsed = format!("{:?}\n", t0.elapsed().as_micros());
        out_stream.write(&elapsed.into_bytes()).unwrap();
    }
    out_stream.flush().unwrap();
    println!("PUT DONE");

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
