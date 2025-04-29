use crate::{
    init_and_mount_pm_fs,
    kv_interface::{Key, KvInterface, Value},
    unmount_pm_fs, MicrobenchmarkConfig, TestValue, VALUE_LEN,
};
use core::marker::PhantomData;
use rocksdb::{Options, DB};
use std::path::Path;
use std::thread::sleep;
use std::time::{Duration, Instant};
use capybarakv::pmem::pmcopy_t::PmCopy;

pub struct RocksDbClient<K, V>
where
    K: PmCopy + Key,
    V: PmCopy + Value,
{
    db: DB,
    _options: Options,
    _path: String,
    _key_type: PhantomData<K>,
    _value_type: PhantomData<V>,
}

fn rocksdb_options() -> Options {
    let cpus = num_cpus::get();
    let rocksdb_cpus: i32 = (cpus * 2).try_into().unwrap();

    let mut options = Options::default();
    options.set_allow_mmap_reads(true);
    options.set_allow_mmap_writes(true);
    options.create_if_missing(true);
    options.set_max_background_compactions(rocksdb_cpus);
    options.increase_parallelism(rocksdb_cpus);
    // https://github.com/facebook/rocksdb/blob/b96432aadd2635f3a9643cb7f4497e109fa9d122/java/src/main/java/org/rocksdb/ColumnFamilyOptionsInterface.java#L545
    options.optimize_level_style_compaction(512 * 1024 * 1024);
    // options.set_max_background_jobs(4);
    // options.set_enable_pipelined_write(true);

    // NOTE: this option doesn't work on the test VM, but it can be disabled
    // when not measuring performance.
    options.set_env(&rocksdb::Env::default_dcpmm().unwrap());

    options
}

impl<K, V> KvInterface<K, V> for RocksDbClient<K, V>
where
    K: PmCopy + Key + AsRef<[u8]>,
    V: PmCopy + Value + AsRef<[u8]>,
{
    type E = rocksdb::Error;

    fn start(config: &MicrobenchmarkConfig) -> Result<Self, Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        init_and_mount_pm_fs(&mount_point, &pm_dev);

        let options = rocksdb_options();

        let db = DB::open(&options, mount_point)?;
        Ok(Self {
            db,
            _options: options,
            _path: mount_point.to_string(),
            _key_type: PhantomData,
            _value_type: PhantomData,
        })
    }

    fn timed_start(config: &MicrobenchmarkConfig) -> Result<(Self, Duration), Self::E> {
        let mount_point = &config.mount_point;
        let pm_dev = &config.pm_dev;

        init_and_mount_pm_fs(&mount_point, &pm_dev);

        let t0 = Instant::now();
        let mut options = rocksdb_options();

        // NOTE: this option doesn't work on the test VM, but it can be disabled
        // when not measuring performance.
        options.set_env(&rocksdb::Env::default_dcpmm()?);

        let db = DB::open(&options, mount_point)?;
        let dur = t0.elapsed();
        Ok((
            Self {
                db,
                _options: options,
                _path: mount_point.to_string(),
                _key_type: PhantomData,
                _value_type: PhantomData,
            },
            dur,
        ))
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
        self.db.flush().unwrap();
    }

    fn cleanup(mount_point: &str, pm_dev: &str) {
        let _ = DB::destroy(&Options::default(), mount_point);
        sleep(Duration::from_secs(1));
        unmount_pm_fs(pm_dev);
    }
}
