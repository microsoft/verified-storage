use storage_node::kv2::impl_t::*;
use storage_node::kv2::spec_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use crate::{Key, Value, KvInterface, init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

use std::fmt::Debug;
use std::hash::Hash;
use std::thread::sleep;
use std::time::{Duration, Instant};
use std::process::Command;

use serde::Deserialize;
use std::fs;
use toml;


// Reusing the same/similar configuration strcts from ycsb_ffi just 
// to keep all of the config files we are using consistent.
// the experiment and DB options are separate in that crate
// so that everything works properly with YCSB
#[derive(Deserialize, Debug)]
pub struct CapybaraKvConfig {
    capybarakv_config: DbOptions,
    experiment_config: ExperimentOptions
}

#[derive(Deserialize, Debug)]
struct ExperimentConfig {
    experiment_config: ExperimentOptions,
}

#[derive(Deserialize, Debug)]
struct DbOptions {
    kv_file: String,
    num_keys: u64, 
    region_size: u64, 
    num_list_entries: u64,
    max_ops_per_transaction: u64
}

// Most of these options are not used at all in this crate,
// but a few are, and reading from this config file makes it 
// easier to ensure that we use the same configurations everywhere
#[allow(dead_code)]
#[derive(Deserialize, Debug)]
struct ExperimentOptions {
    results_dir: String,
    threads: Option<u64>,
    mount_point: String,
    pm_device: String,
    iterations: Option<u64>,
    op_count: Option<u64>,
    record_count: Option<u64>,
}

// TODO: read these from config file
const KVSTORE_ID: u128 = 1234;
const KVSTORE_FILE: &str = "/mnt/pmem/capybarakv";
const REGION_SIZE: u64 = 1024*1024*1024*115;
const NUM_LIST_ENTRIES: u64 = 1000; 
const MAX_OPERATIONS_PER_TRANSACTION: u64 = 5;

// TODO: should make a capybarakv util crate so that you
// can share some of these functions with ycsb_ffi?

pub struct CapybaraKvClient<K, V, L> 
    where 
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
        L: PmCopy + Debug + LogicalRange,
{
    kv: KvStore::<FileBackedPersistentMemoryRegion, K, V, L>,
}

impl<K, V, L> KvInterface<K, V> for CapybaraKvClient<K, V, L>
    where 
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
        L: PmCopy + Debug + LogicalRange,
{
    type E = KvError;

    fn setup(num_keys: u64) -> Result<(), Self::E> {
        init_and_mount_pm_fs();

        let setup_parameters = SetupParameters {
            kvstore_id: KVSTORE_ID,
            logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
            num_keys,
            num_list_entries: NUM_LIST_ENTRIES,
            max_operations_per_transaction: MAX_OPERATIONS_PER_TRANSACTION,
        };

        let mut kv_region = create_pm_region(KVSTORE_FILE, REGION_SIZE);
        KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::setup(
            &mut kv_region, &setup_parameters
        )?;

        Ok(())
    }

    fn start() -> Result<Self, Self::E> {
        let region = open_pm_region(KVSTORE_FILE, REGION_SIZE);
        let kv = KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::start(
            region, KVSTORE_ID)?;
        
        Ok(Self { kv })
    }

    fn timed_start() -> Result<(Self, Duration), Self::E> {
        // init_and_mount_pm_fs();
        remount_pm_fs();

        let t0 = Instant::now();
        // let mut kv_region = create_pm_region(KVSTORE_FILE, REGION_SIZE);
        // KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::setup(
        //     &mut kv_region, KVSTORE_ID, crate::NUM_KEYS + 1, 1, 1
        // )?;

        let region = open_pm_region(KVSTORE_FILE, REGION_SIZE);
        let kv = KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::start(
            region, KVSTORE_ID)?;
        let dur = t0.elapsed();

        Ok((Self { kv } , dur))
    }

    fn db_name() -> String {
        "capybarakv".to_string()
    }

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        self.kv.tentatively_create(key, value)?;
        self.kv.commit()
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        let value = self.kv.read_item(key)?;
        Ok(value)
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        self.kv.tentatively_update_item(key, value)?;
        self.kv.commit()
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        self.kv.tentatively_delete(key)?;
        self.kv.commit()
    }

    fn cleanup() {
        sleep(Duration::from_secs(1));
        unmount_pm_fs();
    }

    fn flush(&mut self) {}
}

// TODO: make these part of the KvInterface trait?
impl<K, V, L> CapybaraKvClient<K, V, L>
    where 
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
        L: PmCopy + Debug + LogicalRange,
{
    // TODO: use this as the main trait setup fn
    pub fn setup_from_config_file(config_file_path: &str) -> Result<CapybaraKvConfig, KvError> {
        let capybarakv_config_contents = match fs::read_to_string(&config_file_path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Could not read file `{}`: {}", config_file_path, e);
                panic!();
            }
        };
        let capybarakv_config: CapybaraKvConfig = toml::from_str(&capybarakv_config_contents).unwrap();
        
        init_and_mount_pm_fs_from_config(&capybarakv_config.experiment_config);

        let setup_parameters = SetupParameters {
            kvstore_id: KVSTORE_ID,
            logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
            num_keys: capybarakv_config.capybarakv_config.num_keys,
            num_list_entries: capybarakv_config.capybarakv_config.num_list_entries,
            max_operations_per_transaction: capybarakv_config.capybarakv_config.max_ops_per_transaction,
        };

        let kvstore_file = capybarakv_config.experiment_config.mount_point.clone() + "/" +
            &capybarakv_config.capybarakv_config.kv_file.clone();
        

        let mut kv_region = create_pm_region(&kvstore_file, capybarakv_config.capybarakv_config.region_size);
        KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::setup(
            &mut kv_region, &setup_parameters
        )?;

        Ok(capybarakv_config)
    }

    pub fn start_from_config(config: &CapybaraKvConfig) -> Result<Self, KvError> {
        let kvstore_file = config.experiment_config.mount_point.clone() + "/" +
            &config.capybarakv_config.kv_file;
        let region = open_pm_region(&kvstore_file, 
            config.capybarakv_config.region_size);
        let kv = KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::start(
            region, KVSTORE_ID)?;
        
        Ok(Self { kv })
    }

    pub fn cleanup_from_config(config: &CapybaraKvConfig) {
        sleep(Duration::from_secs(1));
        unmount_pm_fs_from_config(&config.experiment_config);
    }

    pub fn append_to_list(&mut self, key: &K, list_entry: L) -> Result<(), KvError> {
        self.kv.tentatively_append_to_list(key, list_entry)?;
        self.kv.commit()
    }

    pub fn update_list_entry_at_index(
        &mut self, 
        key: &K, 
        idx: usize, 
        list_entry: L
    ) -> Result<(), KvError> {
        self.kv.tentatively_update_list_entry_at_index(key, idx, list_entry)?;
        self.kv.commit()
    }

    pub fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize
    ) -> Result<(), KvError> {
        self.kv.tentatively_trim_list(key, trim_length)?;
        self.kv.commit()
    }

    pub fn read_list(&mut self, key: &K) -> Result<Vec<L>, KvError> {
        self.kv.read_list(key)
    }

    pub fn get_list_length(&mut self, key: &K) -> Result<usize, KvError> {
        self.kv.get_list_length(key)
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


fn init_and_mount_pm_fs_from_config(config: &ExperimentOptions) {
    println!("Mounting PM FS...");

    unmount_pm_fs();

    println!("Unmounted");

    // Set up PM with a fresh file system instance
    let status = Command::new("sudo")
        .args(["mkfs.ext4", &config.pm_device, "-F"])
        .status()
        .expect("mkfs.ext4 failed");

    let status = Command::new("sudo")
        .args(["mount", "-o", "dax", &config.pm_device, &config.mount_point])
        .status()
        .expect("mount failed");

    let status = Command::new("sudo")
        .args(["chmod", "777", &config.mount_point])
        .status()
        .expect("chmod failed");
    println!("Mounted");
}


fn remount_pm_fs_from_config(config: &ExperimentOptions) {
    println!("Remounting existing FS...");

    unmount_pm_fs();

    println!("Unmounted");

    let status = Command::new("sudo")
        .args(["mount", "-o", "dax", &config.pm_device, &config.mount_point])
        .status()
        .expect("mount failed");

    println!("Mounted");
}

fn unmount_pm_fs_from_config(config: &ExperimentOptions) {
    let status = Command::new("sudo")
        .args(["umount", &config.pm_device])
        .status();
    if let Err(e) = status {
        println!("{:?}", e);
    }
}
