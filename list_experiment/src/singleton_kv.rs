use std::hash::Hash;
use std::ops::Index;
use std::{collections::HashMap, mem::size_of};

use crc64fast::Digest;

use crate::{
    err::Error,
    journal::Journal,
    journaled_singleton_list::*,
    key_table::KeyTable,
    kv::KV,
    list_cache::{ListCache, ListInfo},
    DurableTable, MemoryPool, PmCopy, NULL_ADDR,
};

pub struct SingletonKV<K: PmCopy, const N: usize> {
    // durable stuff
    key_table: KeyTable<K, SingletonMetadata>,
    list_table: SingletonListTable<N>,
    journal: Journal,

    key_index: HashMap<K, IndexMetadata>,
    list_cache: ListCache<N>,
    pending_journal_entries: Vec<(u64, Vec<u8>)>,
}

struct IndexMetadata {
    key_table_index: u64,
    list_head: u64,
}

impl PmCopy for IndexMetadata {}

#[derive(Default, Copy, Clone)]
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
            list_cache: ListCache::new(cache_capacity as usize),
            pending_journal_entries: Vec::new(),
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
        // 1. check that the key exists
        if !self.key_index.contains_key(key) {
            return Err(Error::KeyNotFound);
        }
        let index_metadata = self.key_index.get(key).unwrap();
        let key_table_index = index_metadata.key_table_index;

        // 2. allocate a row in the table
        let new_list_node_row = match self.list_table.allocate() {
            Some(row_addr) => row_addr,
            None => return Err(Error::OutOfSpace),
        };

        // 3. build the new node and write it into the newly-allocated row
        let new_node = DurableSingletonListNode::new(*list_entry);
        let new_node_bytes = new_node.to_bytes();
        let next = NULL_ADDR as u64;
        let next_ptr = DurableSingletonListNodeNextPtr::new(next);
        let next_bytes = next_ptr.to_bytes();

        mem_pool.write(new_list_node_row, new_node_bytes)?;
        mem_pool.write(
            SingletonListTable::<N>::get_next_pointer_offset(new_list_node_row),
            next_bytes,
        )?;
        mem_pool.flush();

        // 4. update the list in the cache and obtain the address of the old tail if it exists.
        // we do this at the same time to avoid calling list_cache.get() twice
        let old_tail = if let Some(list_info) = self.list_cache.get_mut(key_table_index) {
            let old_tail = list_info.tail_addr().cloned();
            list_info.push_new_tail_addr(new_list_node_row);
            old_tail
        } else {
            // this list is not in the cache -- construct its list of addresses
            // including the new one and then put it in the cache
            let mut list_addrs = self.read_list_addrs(mem_pool, key)?;
            let old_tail = list_addrs.last().cloned();
            list_addrs.push(new_list_node_row);
            self.list_cache.put(key_table_index, list_addrs);
            old_tail
        };

        // 5. update other structures via the journal
        // if the list is empty, we need to set its head in the key table
        // if the list is not empty, we need to set the next pointer of
        // the current tail
        if let Some(old_tail) = old_tail {
            // list is not empty. we need to update the next pointer
            // of the old tail
            assert!(old_tail != NULL_ADDR as u64);
            let new_next_tail = DurableSingletonListNodeNextPtr::new(new_list_node_row);
            let new_next_tail_bytes = new_next_tail.to_bytes();
            let next_offset = SingletonListTable::<N>::get_next_pointer_offset(old_tail);
            self.journal
                .append(mem_pool, next_offset, new_next_tail_bytes)?;
            self.pending_journal_entries
                .push((next_offset, new_next_tail_bytes.to_vec()));
        } else {
            // list is empty. we need to update the head in the key table
            // we need to read the whole entry into memory so we can calculate
            // its new CRC

            let (key, metadata) = self.key_table.read(mem_pool, key_table_index)?;
            let mut new_metadata = metadata;
            new_metadata.list_head = new_list_node_row;
            let mut crc_digest = Digest::new();
            crc_digest.write(key.to_bytes());
            crc_digest.write(new_metadata.to_bytes());
            let crc = crc_digest.sum64();

            let metadata_addr = KeyTable::<K, SingletonMetadata>::metadata_addr(key_table_index);
            let crc_addr = KeyTable::<K, SingletonMetadata>::crc_addr(key_table_index);
            self.journal
                .append(mem_pool, metadata_addr, new_metadata.to_bytes())?;
            self.pending_journal_entries
                .push((metadata_addr, new_metadata.to_bytes().to_vec()));
            self.journal
                .append(mem_pool, crc_addr, &crc.to_le_bytes())?;
            self.pending_journal_entries
                .push((crc_addr, crc.to_le_bytes().to_vec()));
        }

        // 6. Commit and apply the journal entries
        self.journal.commit(mem_pool)?;

        self.apply_pending_journal_entries(mem_pool)?;

        self.journal.clear(mem_pool)?;

        Ok(())
    }

    fn trim(&mut self, mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error> {
        todo!()
    }

    fn read_list(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error> {
        todo!()
    }
}

impl<K: PmCopy, const N: usize> SingletonKV<K, N> {
    fn read_list_addrs<P: MemoryPool>(&self, mem_pool: &P, key: &K) -> Result<Vec<u64>, Error> {
        // note: zeroes should not be read into this list
        todo!()
    }

    fn apply_pending_journal_entries<P: MemoryPool>(&self, mem_pool: &mut P) -> Result<(), Error> {
        for (dst, bytes) in &self.pending_journal_entries {
            mem_pool.write(*dst, &bytes)?;
        }

        Ok(())
    }
}
