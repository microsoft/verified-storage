use crate::err::Error;
use crate::journal::Journal;
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

    pub fn get_val(&self) -> [u8; N] {
        self.val
    }
}

impl<const N: usize> PmCopy for DurableBlockListRow<N> {}

#[derive(Debug)]
pub struct DurableBlockListNode<const N: usize, const M: usize> {
    pub vals: [DurableBlockListRow<N>; M],
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

    pub fn next(&self) -> u64 {
        self.next
    }
}

impl PmCopy for DurableBlockListNodeNextPtr {}

pub struct BlockListTable<const N: usize, const M: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize, const M: usize> DurableTable for BlockListTable<N, M> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let block_size = BlockListTable::<N, M>::block_size() as u64;
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
    fn allocate(&mut self) -> Option<u64> {
        self.free_list.pop()
    }

    fn free(&mut self, addr: u64) -> Result<(), Error> {
        if !self.metadata.validate_addr(addr) {
            Err(Error::InvalidAddr)
        } else {
            self.free_list.push(addr);
            Ok(())
        }
    }

    fn row_size() -> usize {
        size_of::<DurableBlockListRow<N>>() // value + CRC
    }

    fn validate_addr(&self, addr: u64) -> bool {
        self.metadata.validate_addr(addr)
    }
}

impl<const N: usize, const M: usize> BlockListTable<N, M> {
    pub fn row_offset_in_block(block_addr: u64, row_index: u64) -> u64 {
        row_index * BlockListTable::<N, M>::row_size() as u64 + block_addr
    }

    pub fn get_next_pointer_offset(block_addr: u64) -> u64 {
        size_of::<DurableBlockListNode<N, M>>() as u64 + block_addr
    }

    fn block_size() -> usize {
        BlockListTable::<N, M>::row_size() * M // rows and their CRCs
            + size_of::<u64>() // CDB
            + size_of::<DurableBlockListNodeNextPtr>() * 2 // two next+CRC areas
    }
}
