use std::collections::HashMap;

use crc64fast::Digest;

use crate::{
    err::Error, journal::Journal, journaled_singleton_list::*, key_table::KeyTable, kv::KV,
    DurableTable, MemoryPool, PmCopy, NULL_ADDR,
};

pub struct SingletonKV<K: PmCopy, const N: usize> {
    // durable stuff
    key_table: KeyTable<K, SingletonMetadata>,
    list_table: SingletonListTable<N>,
    journal: Journal,

    key_to_index: HashMap<K, u64>,
}

struct SingletonMetadata {
    list_head: u64,
}

impl PmCopy for SingletonMetadata {}

impl<P: MemoryPool, K: PmCopy, const N: usize> KV<P, K> for SingletonKV<K, N> {
    fn setup(
        mem_pool: &mut P,
        key_table_size: u64,
        list_table_size: u64,
        journal_size: u64,
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
            key_to_index: HashMap::new(),
        })
    }

    fn insert(&mut self, mem_pool: &mut P, key: &K) -> Result<(), Error> {
        // 1. allocate a slot for the new key in the key table
        let new_key_row = match self.key_table.allocate() {
            Some(row) => row,
            None => return Err(Error::OutOfSpace),
        };

        // 2. set up the metadata and crc
        let metadata = SingletonMetadata {
            list_head: NULL_ADDR as u64,
        };

        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(metadata.to_bytes());
        let crc = crc_digest.sum64();

        // 3. write them to the entry
        mem_pool.write(
            KeyTable::<K, SingletonMetadata>::key_addr(new_key_row),
            key.to_bytes(),
        )?;
        mem_pool.write(
            KeyTable::<K, SingletonMetadata>::metadata_addr(new_key_row),
            metadata.to_bytes(),
        )?;
        mem_pool.write(
            KeyTable::<K, SingletonMetadata>::crc_addr(new_key_row),
            &crc.to_le_bytes(),
        )?;
        mem_pool.flush();

        Ok(())
    }
}
