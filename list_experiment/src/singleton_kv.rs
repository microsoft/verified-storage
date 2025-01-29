use std::fmt::Debug;
use std::hash::Hash;
use std::ops::Index;
use std::{collections::HashMap, mem::size_of};

use crc64fast::Digest;

use crate::{
    err::Error,
    journal::Journal,
    key_table::KeyTable,
    kv::KV,
    list_cache::{ListCache, ListInfo},
    singleton_list::*,
    DurableTable, MemoryPool, PmCopy, NULL_ADDR,
};

pub struct SingletonKV<K: PmCopy + Debug, const N: usize> {
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

// impl PmCopy for IndexMetadata {}

#[derive(Default, Copy, Clone)]
struct SingletonMetadata {
    list_head: u64,
}

impl PmCopy for SingletonMetadata {}

impl<P, K, const N: usize> KV<P, K, N> for SingletonKV<K, N>
where
    P: MemoryPool,
    K: PmCopy + Eq + PartialEq + Hash + Copy + Debug,
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
        let old_tail = if let Some(list_info) = self.list_cache.get(key_table_index) {
            let old_tail = list_info.tail_addr().cloned();
            self.list_cache
                .append_node_addr(key_table_index, new_list_node_row)?;
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
            // we don't have to read from storage here -- we already know the
            // key and have all the info we need to recalculate the CRC

            let new_metadata = SingletonMetadata {
                list_head: new_list_node_row,
            };
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

            let index_metadata = self.key_index.get_mut(&key).unwrap();
            index_metadata.list_head = new_list_node_row;
        }

        // 6. Commit and apply the journal entries
        self.journal.commit(mem_pool)?;

        self.apply_pending_journal_entries(mem_pool)?;

        self.journal.clear(mem_pool)?;

        Ok(())
    }

    fn trim(&mut self, mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error> {
        // 1. check that the key exists
        if !self.key_index.contains_key(key) {
            return Err(Error::KeyNotFound);
        }
        let index_metadata = self.key_index.get(key).unwrap();
        let key_table_index = index_metadata.key_table_index;

        // 2. free the first `trim_len` nodes in the list
        // if we get a cache miss, read the list into the cache first and then trim
        // TODO: would be faster to do the trim simultaneously with the traversal
        // in that case
        let new_head = if let Some(list_info) = self.list_cache.get(key_table_index) {
            let node_addrs = list_info.get_addrs();
            let new_head = node_addrs[trim_len as usize];
            self.free_trimmed_nodes(node_addrs, trim_len)?;
            self.list_cache.trim(key_table_index, trim_len)?;
            new_head
        } else {
            let mut node_addrs = self.read_list_addrs(mem_pool, key)?;
            self.free_trimmed_nodes(&node_addrs, trim_len)?;
            let new_head = node_addrs[trim_len as usize];
            node_addrs.drain(0..trim_len as usize);
            // cache put takes ownership of node addrs, so we only insert it
            // once we have trimmed it
            self.list_cache.put(key_table_index, node_addrs);
            new_head
        };

        let index_metadata = self.key_index.get_mut(&key).unwrap();
        index_metadata.list_head = new_head;

        // 4. update the new head pointer via the journal
        let (key, metadata) = self.key_table.read(mem_pool, key_table_index)?;
        let mut new_metadata = metadata;
        new_metadata.list_head = new_head;
        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(new_metadata.to_bytes());
        let crc = crc_digest.sum64();

        let metadata_addr = KeyTable::<K, SingletonMetadata>::metadata_addr(key_table_index);
        let crc_addr = KeyTable::<K, SingletonMetadata>::crc_addr(key_table_index);

        // append to the journal
        self.journal
            .append(mem_pool, metadata_addr, new_metadata.to_bytes())?;
        self.pending_journal_entries
            .push((metadata_addr, new_metadata.to_bytes().to_vec()));
        self.journal
            .append(mem_pool, crc_addr, &crc.to_le_bytes())?;
        self.pending_journal_entries
            .push((crc_addr, crc.to_le_bytes().to_vec()));

        // 5. Commit and apply the journal entries
        self.journal.commit(mem_pool)?;

        self.apply_pending_journal_entries(mem_pool)?;

        self.journal.clear(mem_pool)?;

        Ok(())
    }

    fn read_list(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error> {
        self.read_full_list(mem_pool, key)
    }
}

impl<K: PmCopy + Eq + PartialEq + Hash + Debug, const N: usize> SingletonKV<K, N> {
    pub fn read_full_list<P: MemoryPool>(
        &self,
        mem_pool: &P,
        key: &K,
    ) -> Result<Vec<[u8; N]>, Error> {
        // 1. check that the key exists
        if !self.key_index.contains_key(key) {
            return Err(Error::KeyNotFound);
        }
        let index_metadata = self.key_index.get(key).unwrap();
        let key_table_index = index_metadata.key_table_index;
        let list_head = index_metadata.list_head;

        let list_info = self.list_cache.get(key_table_index);

        // 2. check if the list is in the cache
        if let Some(list_info) = list_info {
            // the list is in the cache. use the cached addresses to read the nodes
            // TODO: should we store the list contents in the cache as well and
            // check for that before reading from storage?
            let addrs = list_info.get_addrs();
            let mut output_vec = Vec::new();
            for addr in addrs {
                let (val, _) = self.read_node_at_addr(mem_pool, *addr)?;
                output_vec.push(val);
            }
            Ok(output_vec)
        } else {
            // the list is not in the cache. add it to the cache, and read the
            // values to return at the same time
            let (values, addrs) = self.read_list_addrs_and_vals(mem_pool, list_head)?;
            self.list_cache.put(key_table_index, addrs);
            Ok(values)
        }
    }

    fn read_list_addrs_and_vals<P: MemoryPool>(
        &self,
        mem_pool: &P,
        list_head: u64,
    ) -> Result<(Vec<[u8; N]>, Vec<u64>), Error> {
        if list_head != 0 {
            let mut current_node_addr = list_head;
            let mut output_val_vec = Vec::new();
            let mut output_next_vec = Vec::new();

            let (val, next_addr) = self.read_node_at_addr(mem_pool, current_node_addr)?;
            output_val_vec.push(val);
            output_next_vec.push(next_addr);
            current_node_addr = next_addr;

            // read all of the nodes in the list and record their addresses
            while current_node_addr != 0 {
                let (val, next_addr) = self.read_node_at_addr(mem_pool, current_node_addr)?;
                output_val_vec.push(val);
                output_next_vec.push(next_addr);
                current_node_addr = next_addr;
            }

            Ok((output_val_vec, output_next_vec))
        } else {
            Ok((Vec::new(), Vec::new()))
        }
    }

    fn read_list_addrs<P: MemoryPool>(&self, mem_pool: &P, key: &K) -> Result<Vec<u64>, Error> {
        // 1. check that the key exists and look up its list head pointer
        if !self.key_index.contains_key(key) {
            return Err(Error::KeyNotFound);
        }
        let index_metadata = self.key_index.get(key).unwrap();
        let list_head = index_metadata.list_head;

        let mut current_node_addr = list_head;
        let mut output_vec = Vec::new();

        // 2. read all of the nodes in the list and record their addresses
        while current_node_addr != 0 {
            output_vec.push(current_node_addr);
            let (_val, next_addr) = self.read_node_at_addr(mem_pool, current_node_addr)?;
            current_node_addr = next_addr;
        }

        Ok(output_vec)
    }

    fn read_node_at_addr<P: MemoryPool>(
        &self,
        mem_pool: &P,
        addr: u64,
    ) -> Result<([u8; N], u64), Error> {
        // 1. check that the address is valid
        if !self.list_table.validate_addr(addr) {
            return Err(Error::InvalidAddr);
        }

        // TODO: don't read this if you don't have to
        // 2. read the node's value and check its CRC
        let bytes = mem_pool.read(addr, size_of::<DurableSingletonListNode<N>>() as u64)?;
        let node = unsafe { DurableSingletonListNode::<N>::from_bytes(&bytes) };
        if !node.check_crc() {
            return Err(Error::InvalidCRC);
        }

        // 3. read the next pointer and check its CRC
        let bytes = mem_pool.read(
            SingletonListTable::<N>::get_next_pointer_offset(addr),
            size_of::<DurableSingletonListNodeNextPtr>() as u64,
        )?;
        let next_ptr = unsafe { DurableSingletonListNodeNextPtr::from_bytes(&bytes) };
        if !next_ptr.check_crc() {
            return Err(Error::InvalidCRC);
        }

        Ok((node.get_val(), next_ptr.next()))
    }

    fn apply_pending_journal_entries<P: MemoryPool>(&self, mem_pool: &mut P) -> Result<(), Error> {
        for (dst, bytes) in &self.pending_journal_entries {
            mem_pool.write(*dst, &bytes)?;
        }

        Ok(())
    }

    fn free_trimmed_nodes(&mut self, node_addrs: &Vec<u64>, trim_len: u64) -> Result<(), Error> {
        for i in 0..trim_len {
            let addr = node_addrs[i as usize];
            self.list_table.free(addr)?;
        }

        Ok(())
    }
}
