use crate::{err::*, journal::Journal, list::*, mem_pool::*, table::*, CDB_FALSE, CDB_TRUE};
use core::mem::size_of;
use crc64fast::Digest;

pub struct DurableSingletonListNode<const N: usize> {
    val: [u8; N],
    crc: u64,
}

impl<const N: usize> DurableSingletonListNode<N> {
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
        self.val.clone()
    }
}

impl<const N: usize> PmCopy for DurableSingletonListNode<N> {}

#[derive(Debug)]
pub struct DurableSingletonListNodeNextPtr {
    next: u64,
    crc: u64,
}

impl DurableSingletonListNodeNextPtr {
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

impl PmCopy for DurableSingletonListNodeNextPtr {}

pub struct SingletonListTable<const N: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize> DurableTable for SingletonListTable<N> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = SingletonListTable::<N>::row_size() as u64;
        let num_rows = mem_size / row_size;

        let metadata = TableMetadata::new(mem_start, num_rows, row_size);
        let mut free_list = Vec::with_capacity(num_rows as usize);
        for i in 1..num_rows {
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
        size_of::<DurableSingletonListNode<N>>()  // value + CRC
            + size_of::<u64>()  // CDB
            + size_of::<DurableSingletonListNodeNextPtr>() * 2 // two next+CRC areas
    }

    fn validate_addr(&self, addr: u64) -> bool {
        self.metadata.validate_addr(addr)
    }
}

impl<const N: usize> SingletonListTable<N> {
    pub fn get_next_pointer_offset(row_addr: u64) -> u64 {
        size_of::<DurableSingletonListNode<N>>() as u64 + row_addr
    }

    const fn row_size() -> usize {
        size_of::<DurableSingletonListNode<N>>()  // value + CRC
            + size_of::<u64>()  // CDB
            + size_of::<DurableSingletonListNodeNextPtr>() * 2 // two next+CRC areas
    }
}
