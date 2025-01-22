use crate::err::Error;
use crate::list::*;
use crate::mem_pool::*;
use crate::table::*;
use crate::DurableSingletonListNode;
use crate::{CDB_FALSE, CDB_TRUE};
use core::mem::size_of;
use crc64fast::Digest;

#[derive(Copy, Clone, Debug)]
pub struct DurableBlockListRow<const N: usize> {
    val: [u8; N],
    crc: u64,
}

impl<const N: usize> DurableBlockListRow<N> {
    pub fn new(val: [u8; N]) -> Self {
        let mut digest = Digest::new();
        digest.write(&val);
        let crc = digest.sum64();
        Self { val, crc }
    }

    pub fn check_crc(&self) -> bool {
        let mut digest = Digest::new();
        digest.write(&self.val);
        let crc = digest.sum64();
        crc == self.crc
    }
}

impl<const N: usize> PmCopy for DurableBlockListRow<N> {}

#[derive(Debug)]
pub struct DurableBlockListNode<const N: usize, const M: usize> {
    vals: [DurableBlockListRow<N>; M],
}

impl<const N: usize, const M: usize> PmCopy for DurableBlockListNode<N, M> {}

#[derive(Debug)]
pub struct DurableBlockListNodeNextPtr {
    next: u64,
    crc: u64,
}

impl DurableBlockListNodeNextPtr {
    pub fn new(next: u64) -> Self {
        let mut digest = Digest::new();
        digest.write(&next.to_le_bytes());
        let crc = digest.sum64();

        Self { next, crc }
    }

    pub fn check_crc(&self) -> bool {
        let mut digest = Digest::new();
        digest.write(&self.next.to_le_bytes());
        let crc = digest.sum64();
        crc == self.crc
    }
}

impl PmCopy for DurableBlockListNodeNextPtr {}

pub struct BlockListTable<const N: usize, const M: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize, const M: usize> ListTable for BlockListTable<N, M> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let block_size = DurableBlockList::<N, M>::block_size() as u64;
        let num_blocks = mem_size / block_size;

        let metadata = TableMetadata::new(mem_start, num_blocks, block_size);
        let mut free_list = Vec::with_capacity(num_blocks as usize);
        for i in 1..num_blocks {
            free_list.push(metadata.row_index_to_addr(i));
        }

        Self {
            metadata,
            free_list,
        }
    }

    // This function allocates and returns a free row in the table, returning None
    // if the table is full.
    // Note that it returns the absolute address of the row, not the row index.
    fn allocate_node(&mut self) -> Option<u64> {
        self.free_list.pop()
    }

    fn free_node(&mut self, addr: u64) -> Result<(), Error> {
        if !self.metadata.validate_addr(addr) {
            Err(Error::InvalidAddr)
        } else {
            self.free_list.push(addr);
            Ok(())
        }
    }
}

pub struct DurableBlockList<const N: usize, const M: usize> {
    head_addr: u64,
    tail_addr: u64,
    len: u64,
    offset_of_first_entry: u64,
    num_valid_elements_in_tail: u64,
}

impl<const N: usize, const M: usize> DurableBlockList<N, M> {
    pub fn new() -> Self {
        Self {
            head_addr: NULL_ADDR.try_into().unwrap(),
            tail_addr: NULL_ADDR.try_into().unwrap(),
            len: 0,
            offset_of_first_entry: 0,
            num_valid_elements_in_tail: 0,
        }
    }

    const fn row_size() -> usize {
        size_of::<DurableBlockListRow<N>>() // value + CRC
    }

    const fn block_size() -> usize {
        Self::row_size() * M // rows and their CRCs
            + size_of::<u64>() // CDB
            + size_of::<DurableBlockListNodeNextPtr>() * 2 // two next+CRC areas
    }

    fn cdb_offset(block_addr: u64) -> u64 {
        // size_of::<DurableSingletonListNode<N>>() as u64 + row_addr
        size_of::<DurableBlockListNode<N, M>>() as u64 + block_addr
    }

    fn cdb_true_offset(block_addr: u64) -> u64 {
        Self::cdb_offset(block_addr) + size_of::<u64>() as u64
    }

    fn cdb_false_offset(block_addr: u64) -> u64 {
        Self::cdb_true_offset(block_addr) + size_of::<DurableBlockListNodeNextPtr>() as u64
    }

    fn get_next_pointer_offset(block_addr: u64, cdb: u64) -> u64 {
        if cdb == CDB_TRUE {
            Self::cdb_true_offset(block_addr)
        } else {
            Self::cdb_false_offset(block_addr)
        }
    }

    fn row_offset_in_block(block_addr: u64, row_index: u64) -> u64 {
        row_index * Self::row_size() as u64 + block_addr
    }

    pub fn append<P: MemoryPool>(
        &mut self,
        mem_pool: &mut P,
        table: &mut BlockListTable<N, M>,
        val: &[u8; N],
    ) -> Result<(), Error> {
        if self.len > 0 {
            // there is already at least one node in the list

            // determine if there is space in the tail for the new value
            if self.num_valid_elements_in_tail < M as u64 {
                // there is space in the tail for the new element
                let new_row_index = self.num_valid_elements_in_tail;
                let addr = Self::row_offset_in_block(self.tail_addr, new_row_index);
                let new_element = DurableBlockListRow::new(*val);
                let new_element_bytes = new_element.to_bytes();

                mem_pool.write(addr, new_element_bytes)?;

                // we need to update the length of the list and the count of
                // valid elements in the tail block, but not the tail addr, since
                // we did not allocate a new block.
                self.len += 1;
                self.num_valid_elements_in_tail += 1;
            } else {
                // there is not space in the tail for the new element.
                // we need to allocate a new block and append it as the tail
                let new_block_addr = match table.allocate_node() {
                    Some(node_addr) => node_addr,
                    None => return Err(Error::OutOfSpace),
                };

                // write the new element to the first row in the block
                let addr = Self::row_offset_in_block(new_block_addr, 0);
                let new_element = DurableBlockListRow::new(*val);
                let new_element_bytes = new_element.to_bytes();
                mem_pool.write(addr, new_element_bytes)?;

                // we also have to set up the cdb and tail pointer for the new node
                let cdb = CDB_FALSE;
                let next = NULL_ADDR as u64;
                let next_ptr = DurableBlockListNodeNextPtr::new(next);
                let cdb_bytes = cdb.to_le_bytes();
                let next_bytes = next_ptr.to_bytes();

                mem_pool.write(Self::cdb_offset(new_block_addr), &cdb_bytes)?;
                mem_pool.write(Self::cdb_false_offset(new_block_addr), &next_bytes)?;

                // now, update the previous tail to point to the new tail.
                let old_tail_block_addr = self.tail_addr;
                let old_tail_node_cdb_bytes = mem_pool
                    .read(
                        Self::cdb_offset(old_tail_block_addr),
                        size_of::<u64>() as u64,
                    )?
                    .try_into()
                    .unwrap();
                let old_tail_cdb = u64::from_le_bytes(old_tail_node_cdb_bytes);
                let (new_cdb, new_next_offset) = if old_tail_cdb == CDB_FALSE {
                    (CDB_TRUE, Self::cdb_true_offset(old_tail_block_addr))
                } else if old_tail_cdb == CDB_TRUE {
                    (CDB_FALSE, Self::cdb_false_offset(old_tail_block_addr))
                } else {
                    return Err(Error::InvalidCDB);
                };

                let new_next_tail = DurableBlockListNodeNextPtr::new(new_block_addr);
                let new_next_tail_bytes = new_next_tail.to_bytes();

                mem_pool.write(new_next_offset, new_next_tail_bytes)?;
                mem_pool.write(
                    Self::cdb_offset(old_tail_block_addr),
                    &new_cdb.to_le_bytes(),
                )?;

                // increment the list length and set the new tail.
                // we also need to update the number of valid entries in the tail
                self.len += 1;
                self.tail_addr = new_block_addr;
                self.num_valid_elements_in_tail = 1;
            }
        } else {
            // the list is empty. we need to set up the head node
            // allocate a new block to be the head node
            let new_block_addr = match table.allocate_node() {
                Some(node_addr) => node_addr,
                None => return Err(Error::OutOfSpace),
            };
            // write the new element to the first row in the block
            let addr = Self::row_offset_in_block(new_block_addr, 0);
            let new_element = DurableBlockListRow::new(*val);
            let new_element_bytes = new_element.to_bytes();
            mem_pool.write(addr, new_element_bytes)?;

            // set up the CDB and null next pointer
            let cdb = CDB_FALSE;
            let next = NULL_ADDR as u64;
            let next_ptr = DurableBlockListNodeNextPtr::new(next);
            let cdb_bytes = cdb.to_le_bytes();
            let next_bytes = next_ptr.to_bytes();

            mem_pool.write(Self::cdb_offset(new_block_addr), &cdb_bytes)?;
            mem_pool.write(Self::cdb_false_offset(new_block_addr), &next_bytes)?;

            // set up the volatile state.
            self.len += 1;
            self.head_addr = new_block_addr;
            self.tail_addr = new_block_addr;
            self.num_valid_elements_in_tail = 1;
            self.offset_of_first_entry = 0;
        }

        Ok(())
    }

    pub fn trim<P: MemoryPool>(
        &mut self,
        mem_pool: &mut P,
        table: &mut BlockListTable<N, M>,
        trim_len: u64,
    ) -> Result<(), Error> {
        // check that the list is long enough to trim this many elements
        if trim_len > self.len {
            return Err(Error::ListTooShort);
        }

        let mut current_addr = self.head_addr;
        let mut num_trimmed;

        // determine how many elements are in the head node
        // and how many should be trimmed. if it's all of them,
        // we'll free the head; if not, we'll just update the
        // offset of the first entry
        let valid_elements_in_head = if self.head_addr == self.tail_addr {
            self.num_valid_elements_in_tail
        } else {
            M as u64 - self.offset_of_first_entry
        };

        if valid_elements_in_head > trim_len {
            // after trimming, there is still at least one valid
            // node in the head
            self.offset_of_first_entry += trim_len;
            if self.head_addr == self.tail_addr {
                self.num_valid_elements_in_tail -= trim_len;
            }
            num_trimmed = trim_len;
        } else {
            // trimming will require us to free the head node
            num_trimmed = valid_elements_in_head;
            let (_next_node, next_addr) = self.read_block_at_addr(mem_pool, table, current_addr)?;
            table.free_node(current_addr)?;
            current_addr = next_addr;
            self.offset_of_first_entry = 0;
        }

        while num_trimmed < trim_len {
            // determine if we need to deallocate the whole current block
            // or just part of it
            let valid_elements_in_current_node = if current_addr == self.tail_addr {
                self.num_valid_elements_in_tail
            } else {
                M as u64
            };
            if trim_len - num_trimmed >= valid_elements_in_current_node {
                // we need to free the whole block
                let (_next_node, next_addr) =
                    self.read_block_at_addr(mem_pool, table, current_addr)?;
                table.free_node(current_addr)?;
                current_addr = next_addr;
                num_trimmed += valid_elements_in_current_node;
            } else {
                // we will keep the current block but invalidate
                // some of its elements. this should only happen
                // if we're in the tail node. we've already taken
                // care of the head node, so we can assume that
                // the first valid entry is at 0.
                let left_to_trim = trim_len - num_trimmed;
                self.offset_of_first_entry = left_to_trim;
                num_trimmed += left_to_trim;
            }
        }

        self.head_addr = current_addr;
        if current_addr == NULL_ADDR as u64 {
            self.tail_addr = current_addr;
        }
        self.len -= num_trimmed;

        Ok(())
    }

    fn read_block_at_addr<P: MemoryPool>(
        &self,
        mem_pool: &P,
        table: &BlockListTable<N, M>,
        addr: u64,
    ) -> Result<([DurableBlockListRow<N>; M], u64), Error> {
        // 1. check if the address is valid
        if !table.metadata.validate_addr(addr) {
            return Err(Error::InvalidAddr);
        }

        // 2. read the entire block. We'll check row CRCs later
        let bytes = mem_pool.read(addr, size_of::<DurableBlockListNode<N, M>>() as u64)?;
        let node = unsafe { DurableBlockListNode::from_bytes(&bytes) };

        // 3. read the CDB
        let bytes = mem_pool
            .read(Self::cdb_offset(addr), size_of::<u64>() as u64)?
            .try_into()
            .unwrap();
        let cdb = u64::from_le_bytes(bytes);
        if cdb != CDB_FALSE && cdb != CDB_TRUE {
            return Err(Error::InvalidCDB);
        }
        let next_ptr_addr = Self::get_next_pointer_offset(addr, cdb);

        // 4. read the next pointer and check its CRC
        let bytes = mem_pool.read(
            next_ptr_addr,
            size_of::<DurableBlockListNodeNextPtr>() as u64,
        )?;
        let next_ptr = unsafe { DurableBlockListNodeNextPtr::from_bytes(&bytes) };
        if !next_ptr.check_crc() {
            return Err(Error::InvalidCRC);
        }

        Ok((node.vals, next_ptr.next))
    }

    pub fn read_full_list<P: MemoryPool>(
        &self,
        mem_pool: &P,
        table: &BlockListTable<N, M>,
    ) -> Result<Vec<[u8; N]>, Error> {
        if self.head_addr == 0 {
            Ok(Vec::new())
        } else {
            let mut output_vec = Vec::with_capacity(self.len as usize);
            let current_addr = self.head_addr;

            let (vals, mut next_addr) = self.read_block_at_addr(mem_pool, table, current_addr)?;
            // not all of the entries in vals contain an element -- we need
            // to check where to start and check the CRCs here
            let first_index: usize = self.offset_of_first_entry as usize;
            // if the head and the tail are the same, need to consider both the offset
            // of the first entry and the number of valid entries
            let valid_entries_in_block: usize = if current_addr == self.tail_addr {
                self.num_valid_elements_in_tail as usize
            } else {
                M - first_index
            };
            for i in first_index..first_index + valid_entries_in_block {
                let node = vals[i];
                if !node.check_crc() {
                    return Err(Error::InvalidCRC);
                } else {
                    output_vec.push(node.val);
                }
            }

            // in the loop, we don't have to check the offset of the first
            // entry, but we do have to check if the block is the tail and
            // if it is full
            while next_addr != 0 {
                let (vals, new_next_addr) = self.read_block_at_addr(mem_pool, table, next_addr)?;
                let valid_entries_in_block: usize = if next_addr == self.tail_addr {
                    self.num_valid_elements_in_tail as usize
                } else {
                    M
                };

                for i in 0..valid_entries_in_block {
                    let node = vals[i];
                    if !node.check_crc() {
                        return Err(Error::InvalidCRC);
                    } else {
                        output_vec.push(node.val);
                    }
                }

                next_addr = new_next_addr;
            }

            Ok(output_vec)
        }
    }
}
