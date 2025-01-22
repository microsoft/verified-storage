use crate::err::Error;
use crate::list::*;
use crate::table::*;

pub struct DurableBlockListNode<const N: usize, const M: usize> {
    vals: [[u8; N]; M],
    crc: u64,
    next: u64,
}

pub struct VolatileBlockListNode<const N: usize, const M: usize> {
    val: [[u8; N]; M],
    next: Option<Box<VolatileBlockListNode<N, M>>>,
}

impl<const N: usize, const M: usize> VolatileListNode for VolatileBlockListNode<N, M> {
    fn next(&self) -> Option<&Self> {
        match &self.next {
            None => None,
            Some(node) => Some(&node),
        }
    }
}

pub struct BlockListTable<const N: usize, const M: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize, const M: usize> ListTable for BlockListTable<N, M> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = std::mem::size_of::<DurableBlockListNode<N, M>>()
            .try_into()
            .unwrap();
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
    fn allocate_row(&mut self) -> Option<u64> {
        self.free_list.pop()
    }

    fn free_row(&mut self, addr: u64) -> Result<(), Error> {
        if !self.metadata.validate_addr(addr) {
            Err(Error::InvalidAddr)
        } else {
            self.free_list.push(addr);
            Ok(())
        }
    }
}
