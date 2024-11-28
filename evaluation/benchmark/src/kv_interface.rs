use storage_node::pmem::pmcopy_t::PmCopy;
use std::time::Duration;

pub trait KvInterface<K, V> : Sized 
    where 
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    type E;

    fn setup(num_keys: u64) -> Result<(), Self::E> { Ok(()) }

    // Initialize the KV store and return an instance of itself.
    // We'll always build KVs from scratch in these tests, so we'll 
    // do both setup and start (if they are separate) in this function.
    fn start() -> Result<Self, Self::E>;

    // Same as init, except records how long it takes to run init excluding
    // PM FS setup time and returns the duration alongside the KV
    fn timed_start() -> Result<(Self, Duration), Self::E>;

    fn db_name() -> String;

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E>;

    fn get(&mut self, key: &K) -> Result<V, Self::E>;

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E>;

    fn delete(&mut self, key: &K) -> Result<(), Self::E>;

    // RocksDB and CapybaraKV use a cleanup function *after* the KV
    // itself has been dropped. Redis can kill the server and clean up
    // in its Drop impl, but the other two need to drop the KV first.
    fn cleanup();

    // Only required for RocksDB to make updates visible for subsequent ops
    // TODO @hayley -- is this necessary after EVERY put in rocksdb??
    fn flush(&mut self);
}

pub trait Key {
    fn key_str(&self) -> &str;
}

pub trait Value {
    fn field_str(&self) -> &str;

    fn value_str(&self) -> &str;

    fn from_byte_vec(v: Vec<u8>) -> Self;
}