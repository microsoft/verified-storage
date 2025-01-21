use crate::{err::*, list::*, mem_pool::*, table::*, CDB_FALSE, CDB_TRUE};
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
}

impl<const N: usize> PmCopy for DurableSingletonListNode<N> {}

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
}

impl PmCopy for DurableSingletonListNodeNextPtr {}

pub struct VolatileSingletonListNode<const N: usize> {
    val: [u8; N],
    next: Option<Box<VolatileSingletonListNode<N>>>,
}

impl<const N: usize> VolatileListNode for VolatileSingletonListNode<N> {
    fn next(&self) -> Option<&Self> {
        match &self.next {
            None => None,
            Some(node) => Some(&node),
        }
    }
}

pub struct SingletonListTable<const N: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize> ListTable for SingletonListTable<N> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = DurableSingletonList::<N>::row_size().try_into().unwrap();
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
}

pub struct DurableSingletonList<const N: usize> {
    head_addr: u64, // address of the head of the list in the durable table
    tail_addr: u64, // address of the tail of the list in the durable table
    len: u64,
}

impl<const N: usize> DurableSingletonList<N> {
    pub fn new() -> Self {
        Self {
            head_addr: NULL_ADDR.try_into().unwrap(),
            tail_addr: NULL_ADDR.try_into().unwrap(),
            len: 0,
        }
    }

    const fn row_size() -> usize {
        size_of::<DurableSingletonListNode<N>>()  // value + CRC
            + size_of::<u64>()  // CDB
            + size_of::<DurableSingletonListNodeNextPtr>() * 2 // two next+CRC areas
    }

    fn cdb_offset(row_addr: u64) -> u64 {
        size_of::<DurableSingletonListNode<N>>() as u64 + row_addr
    }

    fn cdb_false_offset(row_addr: u64) -> u64 {
        size_of::<DurableSingletonListNode<N>>() as u64 + size_of::<u64>() as u64 + row_addr
    }

    fn cdb_true_offset(row_addr: u64) -> u64 {
        size_of::<DurableSingletonListNode<N>>() as u64
            + size_of::<u64>() as u64
            + size_of::<DurableSingletonListNodeNextPtr>() as u64
            + row_addr
    }

    pub fn append<M: MemoryPool>(
        &mut self,
        mem_pool: &mut M,
        table: &mut SingletonListTable<N>,
        val: [u8; N],
    ) -> Result<(), Error> {
        // 1. allocate a row in the table. Return an error
        // if there are no free rows
        let new_tail_row_addr = match table.allocate_row() {
            Some(row_addr) => row_addr,
            None => return Err(Error::OutOfSpace),
        };

        // 2. build the new node and write it to the new row

        // value + crc
        let new_node = DurableSingletonListNode::new(val);
        let new_node_bytes = new_node.to_bytes();

        let cdb = CDB_FALSE;
        let next = NULL_ADDR as u64;

        let next_ptr = DurableSingletonListNodeNextPtr::new(next);
        let cdb_bytes = cdb.to_le_bytes();
        let next_bytes = next_ptr.to_bytes();

        // row_addr is an absolute address, not an index, so we can write
        // directly to it. also write the cdb and next ptr
        mem_pool.write(new_tail_row_addr, new_node_bytes)?;
        mem_pool.write(Self::cdb_offset(new_tail_row_addr), &cdb_bytes)?;
        mem_pool.write(Self::cdb_false_offset(new_tail_row_addr), next_bytes)?;

        // 3. update the old tail by updating its inactive next ptr and flipping its CDB
        let old_tail_row_addr: u64 = self.tail_addr as u64;
        let old_tail_node_cdb_bytes: [u8; 8] = mem_pool
            .read(Self::cdb_offset(old_tail_row_addr), size_of::<u64>() as u64)?
            .try_into()
            .unwrap();
        let old_tail_cdb = u64::from_le_bytes(old_tail_node_cdb_bytes);
        let (new_cdb, new_next_offset) = if old_tail_cdb == CDB_FALSE {
            (CDB_TRUE, Self::cdb_true_offset(old_tail_row_addr))
        } else if old_tail_cdb == CDB_TRUE {
            (CDB_FALSE, Self::cdb_false_offset(old_tail_row_addr))
        } else {
            return Err(Error::InvalidCDB);
        };
        let new_next_tail = DurableSingletonListNodeNextPtr::new(new_tail_row_addr);
        let new_next_tail_bytes = new_next_tail.to_bytes();

        mem_pool.write(new_next_offset, new_next_tail_bytes)?;
        mem_pool.write(Self::cdb_offset(old_tail_row_addr), &new_cdb.to_le_bytes())?;

        // 5. update list struct
        self.tail_addr = new_tail_row_addr;
        self.len += 1;

        Ok(())
    }
}
