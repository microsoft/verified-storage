use crate::{
    init_and_mount_pm_fs, remount_pm_fs, unmount_pm_fs, Key, KvInterface, ListKvInterface,
    MicrobenchmarkConfig, Value,
};
use pmcopy::PmCopy;
use capybarakv::kv2::impl_t::*;
use capybarakv::kv2::shardkv_t::*;
use capybarakv::kv2::shardkv_v::*;
use capybarakv::kv2::spec_t::*;
use capybarakv::pmem::linux_pmemfile_t::*;
use capybarakv::pmem::pmcopy_t::*;
use capybarakv::pmem::traits_t::{ConstPmSized, PmSafe, PmSized, UnsafeSpecPmSized};
use capybarakv::kv2::rwkv_t::ConcurrentKvStoreTrait;

use capybarakv::kv2::concurrentspec_t::*;
use capybarakv::kv2::rwkv_v;
// use capybarakv::kv2::rwkv_t::*;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;
use std::path::Path;
use std::thread::sleep;
use std::time::{Duration, Instant};

use vstd::prelude::*;

// TODO: read these from config file
const KVSTORE_ID: u128 = 1234;
const KVSTORE_FILE: &str = "/mnt/pmem/capybarakv";
// const REGION_SIZE: u64 = 1024*1024*1024*115;
const REGION_SIZE: u64 = 1024 * 1024 * 1024 * 7; // TODO: revert

// TODO: should make a capybarakv util crate so that you
// can share some of these functions with ycsb_ffi?

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

impl<K, I, L, Op> ReadLinearizer<K, I, L, Op> for PlaceholderCB
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
        Op: ReadOnlyOperation<K, I, L>
{
    type Completion = Self;

    open spec fn namespaces(self) -> Set<int>
    {
        Set::empty()
    }

    open spec fn pre(self, id: int, op: Op) -> bool
    {
        true
    }

    open spec fn post(
        self,
        completion: Self,
        id: int,
        op: Op,
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

pub struct ShardedCapybaraKvClient<K, V, L>
where
    K: PmCopy + Key + Debug + Hash,
    V: PmCopy + Value + Debug + Hash,
    L: PmCopy + Debug + LogicalRange,
{
    kv: ShardedKvStore<FileBackedPersistentMemoryRegion, K, V, L>,
}

impl<K, V, L> KvInterface<K, V> for ShardedCapybaraKvClient<K, V, L>
where
    K: PmCopy + Key + Debug + Hash,
    V: PmCopy + Value + Debug + Hash,
    L: PmCopy + Debug + LogicalRange,
{
    type E = KvError;

    fn setup(config: &MicrobenchmarkConfig) -> Result<(), Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;
        let num_keys = config.max_keys;

        init_and_mount_pm_fs(&mount_point, &pm_dev);

        let setup_parameters = SetupParameters {
            kvstore_id: KVSTORE_ID,
            logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsPermitted,
            max_keys: num_keys + 1,
            max_list_elements: num_keys * config.per_record_list_len,
            max_operations_per_transaction: config.max_operations_per_transaction,
        };

        let space_needed = capybarakv::kv2::rwkv_v::ConcurrentKvStore::<FileBackedPersistentMemoryRegion, K, V, L>::space_needed_for_setup(&setup_parameters)?;
        if config.capybarakv_region_size < space_needed {
            println!("Your requested configuration requires {:?}B but you have only specified a region size of {:?}B", space_needed, config.capybarakv_region_size);
            return Err(KvError::OutOfSpace);
        } else {
            println!("Requested config uses {:?}B, region size {:?}B", space_needed, config.capybarakv_region_size);
        }

        let pm = create_pm_region(&config.kv_file, config.capybarakv_region_size);
        let mut pms = VecDeque::new();
        pms.push_back(pm);

        let (_ckv, _) = setup::<FileBackedPersistentMemoryRegion, K, V, L>(
            pms,
            &setup_parameters,
            Ghost::assume_new(),
            Ghost::assume_new(),
            Ghost::assume_new(),
        )?;

        Ok(())
    }

    fn start(config: &MicrobenchmarkConfig) -> Result<Self, Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        let pm = open_pm_region(&config.kv_file, config.capybarakv_region_size);
        let mut pms = VecDeque::new();
        pms.push_back(pm);

        let kv = recover::<FileBackedPersistentMemoryRegion, K, V, L>(
            pms,
            KVSTORE_ID,
            Ghost::assume_new(),
            Ghost::assume_new(),
            Ghost::assume_new(),
            Ghost::assume_new(),
        )?;

        Ok(Self { kv })
    }

    fn timed_start(config: &MicrobenchmarkConfig) -> Result<(Self, Duration), Self::E> {
        // init_and_mount_pm_fs();
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        remount_pm_fs(&mount_point, &pm_dev);

        let t0 = Instant::now();
        let pm = open_pm_region(&config.kv_file, config.capybarakv_region_size);
        let mut pms = VecDeque::new();
        pms.push_back(pm);
        let kv = recover::<FileBackedPersistentMemoryRegion, K, V, L>(
            pms,
            KVSTORE_ID,
            Ghost::assume_new(),
            Ghost::assume_new(),
            Ghost::assume_new(),
            Ghost::assume_new(),
        )?;
        let dur = t0.elapsed();

        Ok((Self { kv }, dur))
    }

    fn db_name() -> String {
        "capybarakv".to_string()
    }

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        let (result, _) = self
            .kv
            .create(key, value, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        let (result, _) = self
            .kv
            .read_item(key, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        let (result, _) = self
            .kv
            .update_item(key, value, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        let (result, _) = self.kv.delete(key, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn cleanup(mount_point: &str, pm_dev: &str) {
        sleep(Duration::from_secs(1));
        unmount_pm_fs(pm_dev);
    }

    fn flush(&mut self) {}
}

impl<K, V, L> ListKvInterface<K, V, L> for ShardedCapybaraKvClient<K, V, L>
where
    K: PmCopy + Key + Debug + Hash,
    V: PmCopy + Value + Debug + Hash,
    L: PmCopy + Debug + LogicalRange,
{
    fn get_list_length(&mut self, key: &K) -> Result<usize, Self::E> {
        let (result, _) = self
            .kv
            .get_list_length(key, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn read_full_list(&mut self, key: &K) -> Result<Vec<L>, Self::E> {
        let (result, _) = self
            .kv
            .read_list(key, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn append_to_list(&mut self, key: &K, l: L) -> Result<(), Self::E> {
        let (result, _) = self
            .kv
            .append_to_list(key, l, Tracked::<PlaceholderCB>::assume_new());
        result
    }

    fn trim_list(&mut self, key: &K, trim_length: usize) -> Result<(), Self::E> {
        let (result, _) =
            self.kv
                .trim_list(key, trim_length, Tracked::<PlaceholderCB>::assume_new());
        result
    }
}

fn open_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion {
    #[cfg(target_os = "windows")]
    let pm_region = FileBackedPersistentMemoryRegion::restore(
        &file_name,
        MemoryMappedFileMediaType::SSD,
        region_size,
    )
    .unwrap();
    #[cfg(target_os = "linux")]
    let pm_region = FileBackedPersistentMemoryRegion::restore(&file_name, region_size).unwrap();

    pm_region
}

fn create_pm_region(file_name: &str, region_size: u64) -> FileBackedPersistentMemoryRegion {
    #[cfg(target_os = "windows")]
    let pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        MemoryMappedFileMediaType::SSD,
        region_size,
        FileCloseBehavior::TestingSoDeleteOnClose,
    )
    .unwrap();
    #[cfg(target_os = "linux")]
    let pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    )
    .unwrap();

    pm_region
}
