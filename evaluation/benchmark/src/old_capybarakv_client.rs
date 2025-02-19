use storage_node::kv::kvimpl_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use crate::{Key, Value, KvInterface, init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::*;
use storage_node::pmem::traits_t::{ConstPmSized, PmSized, UnsafeSpecPmSized, PmSafe};
use pmsafe::PmCopy;

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
        L: PmCopy + Debug,
{
    kv: KvStore::<FileBackedPersistentMemoryRegion, K, V, L>,
}

impl<K, V, L> KvInterface<K, V> for CapybaraKvClient<K, V, L>
    where 
        K: PmCopy + Key + Debug + Hash,
        V: PmCopy + Value + Debug + Hash,
        L: PmCopy + Debug,
{
    type E = KvError<K>;

    fn setup(num_keys: u64) -> Result<(), Self::E> {
        init_and_mount_pm_fs();

        let mut kv_region = create_pm_region(KVSTORE_FILE, REGION_SIZE);
        KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::setup(
            &mut kv_region, KVSTORE_ID, num_keys + 1, 1, 1
        )?;

        Ok(())
    }

    fn start() -> Result<Self, Self::E> {
        let mut region = open_pm_region(KVSTORE_FILE, REGION_SIZE);
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

        let mut region = open_pm_region(KVSTORE_FILE, REGION_SIZE);
        let kv = KvStore::<FileBackedPersistentMemoryRegion, K, V, L>::start(
            region, KVSTORE_ID)?;
        let dur = t0.elapsed();

        Ok((Self { kv } , dur))
    }

    fn db_name() -> String {
        "capybarakv".to_string()
    }

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        self.kv.create(key, value)?;
        self.kv.commit()
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        let value = self.kv.read_item(key)?;
        Ok(*value)
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        self.kv.update_item(key, value)?;
        self.kv.commit()
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        self.kv.delete(key)?;
        self.kv.commit()
    }

    fn cleanup() {
        sleep(Duration::from_secs(1));
        unmount_pm_fs();
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
