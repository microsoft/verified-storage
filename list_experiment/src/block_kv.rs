use std::hash::Hash;
use std::ops::Index;
use std::{collections::HashMap, mem::size_of};

use crc64fast::Digest;

use crate::{
    block_list::*,
    err::Error,
    journal::Journal,
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

#[derive(Copy, Clone, Debug)]
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

        let mut new_index_metadata = *index_metadata;

        // 2. write the new row, either to an existing node or a newly allocated one
        // if there is no space in the tail (or there is no tail)
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

            let new_row_index = if tail_addr == index_metadata.list_head {
                index_metadata.index_of_first_element + index_metadata.num_live_elem_in_tail
            } else {
                index_metadata.num_live_elem_in_tail
            };
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

        // 3. update the index
        self.key_index.insert(*key, new_index_metadata);

        // 4. update the key table
        let new_durable_metadata = BlockMetadata::from_index_metadata(&new_index_metadata);

        // update key table via journal
        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(new_durable_metadata.to_bytes());
        let crc = crc_digest.sum64();

        let metadata_addr = KeyTable::<K, BlockMetadata>::metadata_addr(key_table_index);
        let crc_addr = KeyTable::<K, BlockMetadata>::crc_addr(key_table_index);

        // 5. append journal entries
        self.journal
            .append(mem_pool, metadata_addr, new_durable_metadata.to_bytes())?;
        self.pending_journal_entries
            .push((metadata_addr, new_durable_metadata.to_bytes().to_vec()));
        self.journal
            .append(mem_pool, crc_addr, &crc.to_le_bytes())?;
        self.pending_journal_entries
            .push((crc_addr, crc.to_le_bytes().to_vec()));

        // 6. commit and apply journal
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
        let index_of_first_element = index_metadata.index_of_first_element;
        let num_live_elem_in_tail = index_metadata.num_live_elem_in_tail;

        // 2. determine how many nodes will be deallocated, the new start index in the head, and the
        // new num of live elements in the tail. These won't ALL change every time, but
        // we'll rewrite the whole data structure that contains them regardless.
        // we first need to get the list of node addrs
        let (new_head, new_index, new_num_live) =
            if let Some(list_info) = self.list_cache.get(key_table_index) {
                // the entry is already in the cache
                let node_addrs = list_info.get_addrs();
                let (to_dealloc, new_index, new_num_live) = self.get_block_trim_numbers(
                    node_addrs,
                    trim_len,
                    index_of_first_element,
                    num_live_elem_in_tail,
                )?;

                self.list_cache.trim(key_table_index, to_dealloc)?;
                self.free_trimmed_nodes(node_addrs, to_dealloc)?;

                if to_dealloc == node_addrs.len() as u64 {
                    (0, 0, 0)
                } else {
                    let new_head = node_addrs[to_dealloc as usize];
                    (new_head, new_index, new_num_live)
                }
            } else {
                // the entry is not in the cache
                let mut node_addrs = self.read_list_addrs(mem_pool, key)?;

                let (to_dealloc, new_index, new_num_live) = self.get_block_trim_numbers(
                    &node_addrs,
                    trim_len,
                    index_of_first_element,
                    num_live_elem_in_tail,
                )?;
                self.free_trimmed_nodes(&node_addrs, to_dealloc)?;
                if to_dealloc == node_addrs.len() as u64 {
                    self.list_cache.put(key_table_index, Vec::new());
                    (0, 0, 0)
                } else {
                    node_addrs.drain(0..to_dealloc as usize);
                    let new_head = node_addrs[0];
                    self.list_cache.put(key_table_index, node_addrs);
                    (new_head, new_index, new_num_live)
                }
            };

        let new_index_metadata = self.key_index.get_mut(key).unwrap();
        new_index_metadata.list_head = new_head;
        new_index_metadata.index_of_first_element = new_index;
        new_index_metadata.num_live_elem_in_tail = new_num_live;

        let new_block_metadata = BlockMetadata::from_index_metadata(&new_index_metadata);

        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(new_block_metadata.to_bytes());
        let crc = crc_digest.sum64();

        let metadata_addr = KeyTable::<K, BlockMetadata>::metadata_addr(key_table_index);
        let crc_addr = KeyTable::<K, BlockMetadata>::crc_addr(key_table_index);

        // append to the journal
        self.journal
            .append(mem_pool, metadata_addr, new_block_metadata.to_bytes())?;
        self.pending_journal_entries
            .push((metadata_addr, new_block_metadata.to_bytes().to_vec()));
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

impl<K: PmCopy + PartialEq + Eq + Hash, const N: usize, const M: usize> BlockKV<K, N, M> {
    fn apply_pending_journal_entries<P: MemoryPool>(&self, mem_pool: &mut P) -> Result<(), Error> {
        for (dst, bytes) in &self.pending_journal_entries {
            mem_pool.write(*dst, &bytes)?;
        }

        Ok(())
    }

    fn read_full_list<P: MemoryPool>(&self, mem_pool: &P, key: &K) -> Result<Vec<[u8; N]>, Error> {
        // 1. check that the key exists
        if !self.key_index.contains_key(key) {
            return Err(Error::KeyNotFound);
        }

        let index_metadata = self.key_index.get(key).unwrap();
        let key_table_index = index_metadata.key_table_index;

        // 2. check if the list is in the cache
        let list_info = self.list_cache.get(key_table_index);

        if let Some(list_info) = list_info {
            // list is in the cache. read the values at the cached addresses
            // without following any stored pointers
            let addrs = list_info.get_addrs();
            let mut output_vec = Vec::new();

            for i in 0..addrs.len() {
                let start_index = if i == 0 {
                    index_metadata.index_of_first_element
                } else {
                    0
                };
                let num_valid_elements = if i == addrs.len() - 1 {
                    index_metadata.num_live_elem_in_tail
                } else if i == 0 {
                    M as u64 - start_index
                } else {
                    M as u64
                };
                let addr = addrs[i];

                let mut vals =
                    self.read_value_at_addr(mem_pool, addr, start_index, num_valid_elements)?;

                output_vec.append(&mut vals);
            }
            Ok(output_vec)
        } else {
            // the list is not in the cache. add it to the cache, and read the
            // values to return at the same time
            let (vals, addrs) = self.read_list_addrs_and_vals(
                mem_pool,
                index_metadata.list_head,
                index_metadata.index_of_first_element,
                index_metadata.num_live_elem_in_tail,
            )?;

            self.list_cache.put(key_table_index, addrs);

            Ok(vals)
        }
    }

    fn read_list_addrs_and_vals<P: MemoryPool>(
        &self,
        mem_pool: &P,
        list_head: u64,
        head_start_index: u64,
        num_live_elem_in_tail: u64,
    ) -> Result<(Vec<[u8; N]>, Vec<u64>), Error> {
        if list_head != 0 {
            let mut current_node_addr = list_head;
            let mut current_start_index = head_start_index;
            let mut output_val_vec = Vec::new();
            let mut output_next_vec = vec![list_head];

            let mut next_ptr = self.read_next(mem_pool, list_head)?;

            while next_ptr != NULL_ADDR as u64 {
                // read starting from the current start index to the end of the node.
                // this node can't be the tail, so we know that all rows in this
                // range are valid.
                let mut values = self.read_value_at_addr(
                    mem_pool,
                    current_node_addr,
                    current_start_index,
                    M as u64 - current_start_index,
                )?;
                output_val_vec.append(&mut values);

                output_next_vec.push(next_ptr);
                current_node_addr = next_ptr;
                current_start_index = 0; // after the head, they all start at 0
                next_ptr = self.read_next(mem_pool, next_ptr)?;
            }

            // current_node_addr is now the tail of the list. read the number
            // of live elements in the tail.
            let mut values = self.read_value_at_addr(
                mem_pool,
                current_node_addr,
                current_start_index,
                num_live_elem_in_tail,
            )?;
            output_val_vec.append(&mut values);

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
            let next_addr = self.read_next(mem_pool, current_node_addr)?;
            current_node_addr = next_addr;
        }

        Ok(output_vec)
    }

    fn read_next<P: MemoryPool>(&self, mem_pool: &P, addr: u64) -> Result<u64, Error> {
        // 1. check that the address is valid
        if !self.list_table.validate_addr(addr) {
            return Err(Error::InvalidAddr);
        }

        self.read_next_ptr_at_addr(mem_pool, addr)
    }

    fn read_value_at_addr<P: MemoryPool>(
        &self,
        mem_pool: &P,
        addr: u64,
        start_index: u64,
        num_values: u64,
    ) -> Result<Vec<[u8; N]>, Error> {
        let mut output_vec = Vec::new();
        let bytes = mem_pool.read(addr, size_of::<DurableBlockListNode<N, M>>() as u64)?;
        let node = unsafe { DurableBlockListNode::<N, M>::from_bytes(&bytes) };

        for i in start_index..start_index + num_values {
            let row = node.vals[i as usize];
            if !row.check_crc() {
                return Err(Error::InvalidCRC);
            }
            output_vec.push(row.get_val());
        }
        Ok(output_vec)
    }

    fn read_next_ptr_at_addr<P: MemoryPool>(&self, mem_pool: &P, addr: u64) -> Result<u64, Error> {
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

    fn read_value_and_next_at_addr<P: MemoryPool>(
        &self,
        mem_pool: &P,
        addr: u64,
        start_index: u64,
        num_values: u64,
    ) -> Result<(Vec<[u8; N]>, u64), Error> {
        // 1. check that the address is valid
        if !self.list_table.validate_addr(addr) {
            return Err(Error::InvalidAddr);
        }

        // 2. read each row in the node, check CRC, and put in the output vec
        let output_vec = self.read_value_at_addr(mem_pool, addr, start_index, num_values)?;

        // 3. read the next pointer and check its CRC
        let next = self.read_next_ptr_at_addr(mem_pool, addr)?;

        Ok((output_vec, next))
    }

    // First u64 in return tuple is the number of physical nodes to deallocate
    // Second u64 in return tuple is the new index_of_first_element value
    // Third u64 in return tuple is the new num_live_elem_in_tail value
    // Return an error if the list is too short to trim `trim_len` elements
    fn get_block_trim_numbers(
        &self,
        node_addrs: &Vec<u64>,
        trim_len: u64,
        index_of_first_element: u64,
        num_live_elem_in_tail: u64,
    ) -> Result<(u64, u64, u64), Error> {
        // length of the list = (node_addrs.len() - 2) * M

        // number of elements in the list (not nodes)
        let list_len = if node_addrs.len() > 2 {
            // the list has more than just a head and tail node
            ((node_addrs.len() as u64 - 2) * M as u64)
                + num_live_elem_in_tail
                + (M as u64 - index_of_first_element)
        } else if node_addrs.len() == 2 {
            // the list has only a head and tail node, and they are different
            num_live_elem_in_tail + (M as u64 - index_of_first_element)
        } else if node_addrs.len() == 1 {
            // the list has a single node, which is both the head and tail
            num_live_elem_in_tail
        } else {
            return Err(Error::ListTooShort);
        };

        // return an error if the trim len is longer than the list
        if list_len < trim_len {
            Err(Error::ListTooShort)
        } else if list_len == trim_len {
            // we're emptying out the list. deallocate all nodes, set the other
            // two values to 0
            Ok((node_addrs.len() as u64, 0, 0))
        } else {
            let mut output_index = index_of_first_element;
            let mut output_num_live = num_live_elem_in_tail;
            let mut dealloc_count = 0;

            // let nodes_in_head = M as u64 - index_of_first_element;
            let nodes_in_head = if node_addrs.len() > 1 {
                M as u64 - index_of_first_element
            } else {
                num_live_elem_in_tail
            };

            if trim_len < M as u64 - index_of_first_element {
                // we are trimming fewer nodes than there are in the head.
                // we need to update the index of the first element but
                // otherwise are done
                output_index += trim_len;
                if node_addrs.len() == 1 {
                    // if this node is the tail node, we need to
                    // update the number of live nodes in it too
                    output_num_live -= trim_len;
                }
                Ok((0, output_index, output_num_live))
            } else {
                // otherwise, we're deallocating the head (and possibly other
                // nodes as well)

                let mut to_trim = trim_len - nodes_in_head;
                dealloc_count += 1; //deallocating at least the head

                // now -- to_trim / M should give us the number of full
                // nodes that we need to deallocate
                let nodes_to_dealloc = to_trim / M as u64;
                dealloc_count += nodes_to_dealloc;
                to_trim -= nodes_to_dealloc * M as u64;

                // the remaining nodes will be in a node we don't deallocate
                // which will become the new head.
                output_index = to_trim; // TODO: I think this will work?

                // we only update the number of live elements in the tail
                // if there is one node left
                if node_addrs.len() as u64 - dealloc_count == 1 {
                    output_num_live = num_live_elem_in_tail - output_index;
                }

                Ok((dealloc_count, output_index, output_num_live))
            }
        }
    }

    fn free_trimmed_nodes(&mut self, node_addrs: &Vec<u64>, to_dealloc: u64) -> Result<(), Error> {
        for i in 0..to_dealloc {
            let addr = node_addrs[i as usize];
            self.list_table.free(addr)?;
        }
        Ok(())
    }
}
