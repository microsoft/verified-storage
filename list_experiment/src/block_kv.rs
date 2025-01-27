use std::hash::Hash;
use std::ops::Index;
use std::{collections::HashMap, mem::size_of};

use crc64fast::Digest;

use crate::{
    err::Error,
    journal::Journal,
    journaled_block_list::*,
    key_table::KeyTable,
    kv::KV,
    list_cache::{ListCache, ListInfo},
    DurableTable, MemoryPool, PmCopy, NULL_ADDR,
};

pub struct BlockKV<K: PmCopy, const N: usize, const M: usize> {
    key_table: KeyTable<K, BlockMetadata>,
    list_table: BlockListTable<N, M>,
    journal: Journal,

    key_index: HashMap<K, IndexMetadata>,
    list_cache: ListCache<N>,
    pending_journal_entries: Vec<(u64, Vec<u8>)>,
}

#[derive(Copy, Clone)]
struct IndexMetadata {
    key_table_index: u64,
    list_head: u64,
    index_of_first_element: u64,
    num_live_elem_in_tail: u64,
}

#[derive(Default, Copy, Clone)]
struct BlockMetadata {
    list_head: u64,
    index_of_first_element: u64,
    num_live_elem_in_tail: u64,
}

impl BlockMetadata {
    fn from_index_metadata(index_metadata: &IndexMetadata) -> Self {
        Self {
            list_head: index_metadata.list_head,
            index_of_first_element: index_metadata.index_of_first_element,
            num_live_elem_in_tail: index_metadata.num_live_elem_in_tail,
        }
    }
}

impl PmCopy for BlockMetadata {}

impl<P, K, const N: usize, const M: usize> KV<P, K, N> for BlockKV<K, N, M>
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
        let list_table = BlockListTable::new(start_addr + key_table_size, list_table_size);
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

    fn insert(&mut self, mem_pool: &mut P, key: &K) -> Result<(), Error> {
        let key_table_row = self.key_table.insert(mem_pool, key)?;

        self.key_index.insert(
            *key,
            IndexMetadata {
                key_table_index: key_table_row,
                list_head: NULL_ADDR as u64,
                index_of_first_element: 0,
                num_live_elem_in_tail: 0,
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
        let list_head = index_metadata.list_head;

        let mut new_index_metadata = *index_metadata;

        // we don't have to allocate -- the list is not empty and there is space in the tail.
        if 0 < index_metadata.num_live_elem_in_tail
            && index_metadata.num_live_elem_in_tail < M as u64
        {
            let tail_addr = self.list_cache.get_tail_addr(key_table_index);
            let tail_addr = if let Some(tail_addr) = tail_addr {
                tail_addr
            } else {
                // cache miss. read the list from storage
                let list_addrs = self.read_list_addrs(mem_pool, key)?;
                let tail_addr = *list_addrs.last().unwrap();
                self.list_cache.put(key_table_index, list_addrs);
                tail_addr
            };

            let new_row_index = index_metadata.num_live_elem_in_tail;
            let new_elem_addr =
                BlockListTable::<N, M>::row_offset_in_block(tail_addr, new_row_index);
            let new_element = DurableBlockListRow::new(*list_entry);
            let new_element_bytes = new_element.to_bytes();

            mem_pool.write(new_elem_addr, new_element_bytes)?;
            mem_pool.flush();

            new_index_metadata.num_live_elem_in_tail += 1;
        } else {
            // either the list is empty, or its tail node is full

            // allocate a new block
            let new_block_addr = match self.list_table.allocate() {
                Some(node_addr) => node_addr,
                None => return Err(Error::OutOfSpace),
            };

            let new_row_index = 0;

            // write the new element and a null next pointer to that block
            let new_elem_addr =
                BlockListTable::<N, M>::row_offset_in_block(new_block_addr, new_row_index);
            let new_element = DurableBlockListRow::new(*list_entry);
            let new_element_bytes = new_element.to_bytes();
            mem_pool.write(new_elem_addr, new_element_bytes)?;

            let next = NULL_ADDR as u64;
            let next_ptr = DurableBlockListNodeNextPtr::new(next);
            let next_bytes = next_ptr.to_bytes();
            mem_pool.write(
                BlockListTable::<N, M>::get_next_pointer_offset(new_block_addr),
                next_bytes,
            )?;
            mem_pool.flush();

            // set up the metadata depending on whether the list was empty or not
            let mut new_index_metadata = *index_metadata;
            if index_metadata.list_head == NULL_ADDR as u64 {
                // list is empty
                new_index_metadata.list_head = new_block_addr;
                new_index_metadata.index_of_first_element = new_row_index;
                new_index_metadata.num_live_elem_in_tail = 1;
            } else {
                // list is not empty
                new_index_metadata.num_live_elem_in_tail = 1;
            }

            // add the new node to the cache
            if self.list_cache.contains(key_table_index) {
                // cache hit. we can just append the new node
                self.list_cache
                    .append_node_addr(key_table_index, new_block_addr)?;
            } else {
                // cache miss. we need to read it into the cache
                let mut list_addrs = self.read_list_addrs(mem_pool, key)?;
                list_addrs.push(new_block_addr);
                self.list_cache.put(key_table_index, list_addrs);
            }
        }

        // update the index
        self.key_index.insert(*key, new_index_metadata);

        // update the key table
        let new_durable_metadata = BlockMetadata::from_index_metadata(&new_index_metadata);

        // update key table via journal
        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(new_durable_metadata.to_bytes());
        let crc = crc_digest.sum64();

        let metadata_addr = KeyTable::<K, BlockMetadata>::metadata_addr(key_table_index);
        let crc_addr = KeyTable::<K, BlockMetadata>::crc_addr(key_table_index);

        // append journal entries
        self.journal
            .append(mem_pool, metadata_addr, new_durable_metadata.to_bytes())?;
        self.pending_journal_entries
            .push((metadata_addr, new_durable_metadata.to_bytes().to_vec()));
        self.journal
            .append(mem_pool, crc_addr, &crc.to_le_bytes())?;
        self.pending_journal_entries
            .push((crc_addr, crc.to_le_bytes().to_vec()));

        // commit and apply journal
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

impl<K: PmCopy + PartialEq + Eq + Hash, const N: usize, const M: usize> BlockKV<K, N, M> {
    fn apply_pending_journal_entries<P: MemoryPool>(&self, mem_pool: &mut P) -> Result<(), Error> {
        for (dst, bytes) in &self.pending_journal_entries {
            mem_pool.write(*dst, &bytes)?;
        }

        Ok(())
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
            let next_addr = self.read_next_node_at_addr(mem_pool, current_node_addr)?;
            current_node_addr = next_addr;
        }

        Ok(output_vec)
    }

    fn read_next_node_at_addr<P: MemoryPool>(&self, mem_pool: &P, addr: u64) -> Result<u64, Error> {
        // 1. check that the address is valid
        if !self.list_table.validate_addr(addr) {
            println!("invalid addr");
            return Err(Error::InvalidAddr);
        }

        // // 2. read the node's value and check its CRC
        // let bytes = mem_pool.read(addr, size_of::<DurableBlockListNode<N, M>>() as u64)?;
        // let node = unsafe { DurableBlockListNode::<N, M>::from_bytes(&bytes) };
        // if !node.check_crc() {
        //     return Err(Error::InvalidCRC);
        // }

        // 3. read the next pointer and check its CRC
        let bytes = mem_pool.read(
            BlockListTable::<N, M>::get_next_pointer_offset(addr),
            size_of::<DurableBlockListNodeNextPtr>() as u64,
        )?;
        let next_ptr = unsafe { DurableBlockListNodeNextPtr::from_bytes(&bytes) };
        if !next_ptr.check_crc() {
            return Err(Error::InvalidCRC);
        }

        Ok(next_ptr.next())
    }
}
