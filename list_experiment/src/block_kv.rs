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

        if list_head != NULL_ADDR as u64 {
            // the list is not empty, but we may have a cache miss

            // 2. obtain the address of the current tail
            let tail_addr = self.list_cache.get_tail_addr(key_table_index);

            // 3. determine if there is space in the tail for the new value.
            // if there is, we can write it there.
            // if not, or the list is empty, we need to allocate a new node.

            let mut need_to_allocate = true;
            if let Some(tail_addr) = tail_addr {
                if index_metadata.num_live_elem_in_tail < M as u64 {
                    // there is space in the tail for the new element, so
                    // we can write it there directly.
                    let new_row_index = index_metadata.num_live_elem_in_tail;
                    let new_elem_addr =
                        BlockListTable::<N, M>::row_offset_in_block(tail_addr, new_row_index);
                    let new_element = DurableBlockListRow::new(*list_entry);
                    let new_element_bytes = new_element.to_bytes();

                    mem_pool.write(new_elem_addr, new_element_bytes)?;
                    mem_pool.flush();
                    need_to_allocate = false;
                }

                new_index_metadata.num_live_elem_in_tail += 1;
            } else {
                // cache miss. read the list from storage
                // TODO @hayley tuesday
            }
        }

        // if need_to_allocate {
        //     // either the list is empty or there wasn't room for the new element
        //     // in the tail node.

        //     // allocate a new block
        //     let new_block_addr = match self.list_table.allocate() {
        //         Some(node_addr) => node_addr,
        //         None => return Err(Error::OutOfSpace),
        //     };

        //     let new_row_index = 0;

        //     // write the new element and a null next pointer to that block
        //     let new_elem_addr =
        //         BlockListTable::<N, M>::row_offset_in_block(new_block_addr, new_row_index);
        //     let new_element = DurableBlockListRow::new(*list_entry);
        //     let new_element_bytes = new_element.to_bytes();
        //     mem_pool.write(new_elem_addr, new_element_bytes)?;

        //     let next = NULL_ADDR as u64;
        //     let next_ptr = DurableBlockListNodeNextPtr::new(next);
        //     let next_bytes = next_ptr.to_bytes();
        //     mem_pool.write(
        //         BlockListTable::<N, M>::get_next_pointer_offset(new_block_addr),
        //         next_bytes,
        //     )?;
        //     mem_pool.flush();

        //     if tail_addr.is_some() {
        //         // list is not empty. we don't have to update the head but
        //         // we DO have to update the cache
        //         new_index_metadata.num_live_elem_in_tail = 1;
        //     } else {
        //         // list is empty, we do have to update the head
        //         new_index_metadata.list_head = new_block_addr;
        //         new_index_metadata.num_live_elem_in_tail = 1;
        //     }
        // }

        // // 4. Update the index and key table
        // // we don't have to read from storage here -- we already know the
        // // key and have all the info we need to recalculate its CRC

        // // update index
        // // we need to obtain the new BlockMetadata before updating the index to
        // // satisfy the borrow checker
        // let new_metadata = BlockMetadata::from_index_metadata(&index_metadata);
        // self.key_index.insert(*key, new_index_metadata);

        // // update key table via journal
        // let mut crc_digest = Digest::new();
        // crc_digest.write(key.to_bytes());
        // crc_digest.write(new_metadata.to_bytes());
        // let crc = crc_digest.sum64();

        // let metadata_addr = KeyTable::<K, BlockMetadata>::metadata_addr(key_table_index);
        // let crc_addr = KeyTable::<K, BlockMetadata>::crc_addr(key_table_index);

        // // append journal entries
        // self.journal
        //     .append(mem_pool, metadata_addr, new_metadata.to_bytes())?;
        // self.pending_journal_entries
        //     .push((metadata_addr, new_metadata.to_bytes().to_vec()));
        // self.journal
        //     .append(mem_pool, crc_addr, &crc.to_le_bytes())?;
        // self.pending_journal_entries
        //     .push((crc_addr, crc.to_le_bytes().to_vec()));

        // // commit and apply journal
        // self.journal.commit(mem_pool)?;
        // self.apply_pending_journal_entries(mem_pool)?;
        // self.journal.clear(mem_pool)?;

        Ok(())
    }

    fn trim(&mut self, mem_pool: &mut P, key: &K, trim_len: u64) -> Result<(), Error> {
        todo!()
    }

    fn read_list(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error> {
        todo!()
    }
}

impl<K: PmCopy, const N: usize, const M: usize> BlockKV<K, N, M> {
    fn apply_pending_journal_entries<P: MemoryPool>(&self, mem_pool: &mut P) -> Result<(), Error> {
        for (dst, bytes) in &self.pending_journal_entries {
            mem_pool.write(*dst, &bytes)?;
        }

        Ok(())
    }
}
