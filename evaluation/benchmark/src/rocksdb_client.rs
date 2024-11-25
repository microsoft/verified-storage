use rocksdb::{DB, Options};
use crate::{
    kv_interface::{KvInterface, Key, Value}, 
    VALUE_LEN, TestValue, init_and_mount_pm_fs, unmount_pm_fs};
use storage_node::pmem::pmcopy_t::PmCopy;
use core::marker::PhantomData;
use std::path::Path;
use std::thread::sleep;
use std::time::{Duration, Instant};

// TODO: get this from a config file
const ROCKSDB_PATH: &str = "/mnt/pmem/";

pub struct RocksDbClient<K, V>
    where 
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    db: DB,
    options: Options,
    path: String,
    _key_type: PhantomData<K>,
    _value_type: PhantomData<V>,
}

impl<K, V> KvInterface<K, V> for RocksDbClient<K, V>
    where 
        K: PmCopy + Key + AsRef<[u8]>,
        V: PmCopy + Value + AsRef<[u8]>,
{
    type E = rocksdb::Error;

    fn start() -> Result<Self, Self::E> {
        init_and_mount_pm_fs();

        let mut options = Options::default();
        options.set_allow_mmap_reads(true);
        options.set_allow_mmap_writes(true);
        options.create_if_missing(true);

        // NOTE: this option doesn't work on the test VM, but it can be disabled
        // when not measuring performance.
        options.set_env(&rocksdb::Env::default_dcpmm()?);

        let db = DB::open(&options, crate::MOUNT_POINT)?;
        Ok(Self { 
            db,
            options,
            path: crate::MOUNT_POINT.to_string(),
            _key_type: PhantomData,
            _value_type: PhantomData,
        })
    }

    fn timed_start() -> Result<(Self, Duration), Self::E> {
        init_and_mount_pm_fs();

        let t0 = Instant::now();
        let mut options = Options::default();
        options.set_allow_mmap_reads(true);
        options.set_allow_mmap_writes(true);
        options.create_if_missing(true);

        // NOTE: this option doesn't work on the test VM, but it can be disabled
        // when not measuring performance.
        options.set_env(&rocksdb::Env::default_dcpmm()?);

        let db = DB::open(&options, crate::MOUNT_POINT)?;
        let dur = t0.elapsed();
        Ok((Self { 
            db,
            options,
            path: crate::MOUNT_POINT.to_string(),
            _key_type: PhantomData,
            _value_type: PhantomData,
        }, dur))
    }

    fn db_name() -> String {
        "pmemrocksdb".to_string()
    }

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        self.db.put(key, value)?;
        Ok(())
    }

    fn get(&mut self, key: &K) -> Result<V, Self::E> {
        let v = self.db.get(key)?;
        let ret = match v {
            Some(v) => V::from_byte_vec(v),
            None => panic!("key does not exist"), // TODO better error handling
        };
        Ok(ret)
    }

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E> {
        // TODO: does this work if the key already exists? this is what 
        // YCSB does, so I think it should work
        self.db.put(key, value)?;
        Ok(())
    }

    fn delete(&mut self, key: &K) -> Result<(), Self::E> {
        self.db.delete(key)?;
        Ok(())
    }

    fn flush(&mut self) {
        self.db.flush();
    }

    fn cleanup() {
        let _ = DB::destroy(&Options::default(), ROCKSDB_PATH);
        sleep(Duration::from_secs(1));
        unmount_pm_fs();
    }
}