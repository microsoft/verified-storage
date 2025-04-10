use storage_node::kv2::impl_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::kv2::spec_t::*;
use crate::{Key, Value, KvInterface, init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, pmcopy};
use pmcopy::PmCopy;

use std::fmt::Debug;
use std::hash::Hash;
use std::thread::sleep;
use std::time::{Duration, Instant};

// TODO: read these from config file
const KVSTORE_ID: u128 = 1234;
const KVSTORE_FILE: &str = "/mnt/pmem/capybarakv";
const REGION_SIZE: u64 = 1024*1024*1024*115;

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

    fn setup(mount_point: &str, pm_dev: &str, num_keys: u64) -> Result<(), Self::E> {
        init_and_mount_pm_fs(mount_point, pm_dev);

        let setup_parameters = SetupParameters {
            kvstore_id: KVSTORE_ID,
            logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
            max_keys: num_keys + 1,
            max_list_elements: 10, // TODO: set this to something that makes sense
            max_operations_per_transaction: 5 // TODO: set this to something that makes sense
        };

        let mut kv_region = create_pm_region(KVSTORE_FILE, REGION_SIZE);
        KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::setup(
            &mut kv_region, &setup_parameters
        )?;

        Ok(())
    }

    fn start(mount_point: &str, pm_dev: &str) -> Result<Self, Self::E> {
        let region = open_pm_region(KVSTORE_FILE, REGION_SIZE);
        let kv = KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::start(
            region, KVSTORE_ID)?;
        
        Ok(Self { kv })
    }

    fn timed_start(mount_point: &str, pm_dev: &str) -> Result<(Self, Duration), Self::E> {
        // init_and_mount_pm_fs();
        remount_pm_fs(mount_point, pm_dev);

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

    fn cleanup(pm_dev: &str) {
        sleep(Duration::from_secs(1));
        unmount_pm_fs(pm_dev);
    }

    fn flush(&mut self) {}
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
