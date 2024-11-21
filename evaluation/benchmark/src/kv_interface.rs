use storage_node::pmem::pmcopy_t::PmCopy;

pub trait KvInterface<K, V> : Sized 
    where 
        K: PmCopy + Key,
        V: PmCopy + Value,
{
    type E;

    // Initialize the KV store and return an instance of itself.
    // We'll always build KVs from scratch in these tests, so we'll 
    // do both setup and start (if they are separate) in this function.
    fn init() -> Result<Self, Self::E>;

    fn db_name() -> String;

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E>;

    fn get(&mut self, key: &K) -> Result<V, Self::E>;

    fn update(&mut self, key: &K, value: &V) -> Result<(), Self::E>;

    fn delete(&mut self, key: &K) -> Result<(), Self::E>;

    // RocksDB requires a cleanup function to run AFTER the RocksDB client
    // has gone out of scope. This associated function should only be 
    // implemented by the RocksDB client and should act like the Drop impl
    // does for the other clients.
    fn cleanup();

    // Also only required for RocksDB to make updates visible for subsequent ops
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