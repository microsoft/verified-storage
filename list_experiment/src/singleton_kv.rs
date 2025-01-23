use std::collections::HashMap;
use std::hash::Hash;

use crc64fast::Digest;

use crate::{
    err::Error, journal::Journal, journaled_singleton_list::*, key_table::KeyTable, kv::KV,
    list_cache::ListCache, DurableTable, MemoryPool, PmCopy, NULL_ADDR,
};

pub struct SingletonKV<K: PmCopy, const N: usize> {
    // durable stuff
    key_table: KeyTable<K, SingletonMetadata>,
    list_table: SingletonListTable<N>,
    journal: Journal,

    key_index: HashMap<K, IndexMetadata>,
    list_cache: ListCache<N>,
}

struct IndexMetadata {
    key_table_index: u64,
    list_head: u64,
}

#[derive(Default)]
struct SingletonMetadata {
    list_head: u64,
}

impl PmCopy for SingletonMetadata {}

impl<P, K, const N: usize> KV<P, K, N> for SingletonKV<K, N>
where
    P: MemoryPool,
    K: PmCopy + Eq + PartialEq + Hash + Copy,
{
    fn setup(
        mem_pool: &mut P,
        key_table_size: u64,
        list_table_size: u64,
        journal_size: u64,
        cache_capacity: u64,
    ) -> Result<Self, Error> {
        if key_table_size + list_table_size + journal_size > mem_pool.len() {
            return Err(Error::InvalidMemPoolSize);
        }

        let start_addr = mem_pool.start_addr();
        let key_table = KeyTable::new(start_addr, key_table_size);
        let list_table = SingletonListTable::new(start_addr + key_table_size, list_table_size);
        let journal = Journal::setup(
            mem_pool,
            start_addr + key_table_size + list_table_size,
            journal_size,
        )?;

        Ok(Self {
            key_table,
            list_table,
            journal,
            key_index: HashMap::new(),
            list_cache: ListCache::new(cache_capacity),
        })
    }

    // In the real implementation this involves the journal, but we aren't
    // measuring the performance of this op here or trying to
    // recover from any failures, so it doesn't matter.
    fn insert(&mut self, mem_pool: &mut P, key: &K) -> Result<(), Error> {
        let key_table_row = self.key_table.insert(mem_pool, key)?;

        self.key_index.insert(
            *key,
            IndexMetadata {
                key_table_index: key_table_row,
                list_head: NULL_ADDR as u64,
            },
        );

        Ok(())
    }

    fn append(&mut self, mem_pool: &mut P, key: &K, list_entry: &[u8; N]) -> Result<(), Error> {
        todo!()
    }

    fn trim(&mut self, mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error> {
        todo!()
    }

    fn read_list(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error> {
        todo!()
    }
}
