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

    fn db_name(&self) -> String;

    fn put(&mut self, key: &K, value: &V) -> Result<(), Self::E>;
}

pub trait Key {
    fn key_str(&self) -> &str;
}

pub trait Value {
    fn field_str(&self) -> &str;

    fn value_str(&self) -> &str;
}