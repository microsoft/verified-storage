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

    pub fn check_crc(&self) -> bool {
        let mut digest = Digest::new();
        digest.write(&self.val);
        let crc = digest.sum64();
        crc == self.crc
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

    pub fn check_crc(&self) -> bool {
        let mut digest = Digest::new();
        digest.write(&self.next.to_le_bytes());
        let crc = digest.sum64();
        crc == self.crc
    }
}

impl PmCopy for DurableSingletonListNodeNextPtr {}

pub struct SingletonListTable<const N: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize> ListTable for SingletonListTable<N> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = DurableSingletonList::<N>::row_size() as u64;
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

    fn get_next_pointer_offset(row_addr: u64, cdb: u64) -> u64 {
        if cdb == CDB_TRUE {
            Self::cdb_true_offset(row_addr)
        } else {
            Self::cdb_false_offset(row_addr)
        }
    }

    pub fn append<M: MemoryPool>(
        &mut self,
        mem_pool: &mut M,
        table: &mut SingletonListTable<N>,
        val: &[u8; N],
    ) -> Result<(), Error> {
        // 1. allocate a row in the table. Return an error
        // if there are no free rows
        let new_tail_row_addr = match table.allocate_node() {
            Some(row_addr) => row_addr,
            None => return Err(Error::OutOfSpace),
        };

        // 2. build the new node and write it to the new row

        // value + crc
        let new_node = DurableSingletonListNode::new(*val);
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
        if old_tail_row_addr != NULL_ADDR as u64 {
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
        } else {
            // if the tail is null, the list is empty, so we
            // need to set the head pointer to the newly-created node.
            self.head_addr = new_tail_row_addr;
        }

        // 5. update list struct
        self.tail_addr = new_tail_row_addr;
        self.len += 1;

        Ok(())
    }

    pub fn trim<M: MemoryPool>(
        &mut self,
        mem_pool: &mut M,
        table: &mut SingletonListTable<N>,
        trim_len: u64,
    ) -> Result<(), Error> {
        // 1. check that the list is long enough to trim this many elements.
        // if it isn't, return an error
        if trim_len > self.len {
            return Err(Error::ListTooShort);
        }

        // 2. free the first `trim_len` nodes in the list
        let mut current_addr = self.head_addr;
        let mut num_trimmed = 0;

        while num_trimmed < trim_len {
            let (_current_node, next_addr) =
                self.read_node_at_addr(mem_pool, table, current_addr)?;

            table.free_node(current_addr)?;

            current_addr = next_addr;

            num_trimmed += 1;
        }

        // 3. set the new head pointer
        self.head_addr = current_addr;

        Ok(())
    }

    // This function returns a volatile node with a `None`` next ptr and
    // the physical location of the next node in the list
    fn read_node_at_addr<M: MemoryPool>(
        &self,
        mem_pool: &M,
        table: &SingletonListTable<N>,
        addr: u64,
    ) -> Result<([u8; N], u64), Error> {
        // 1. check that the address is valid
        if !table.metadata.validate_addr(addr) {
            return Err(Error::InvalidAddr);
        }

        // 2. read the node's value and check its CRC
        let bytes = mem_pool.read(addr, size_of::<DurableSingletonListNode<N>>() as u64)?;
        let node = unsafe { DurableSingletonListNode::from_bytes(&bytes) };
        if !node.check_crc() {
            return Err(Error::InvalidCRC);
        }

        // 3. read the CDB
        let bytes: [u8; 8] = mem_pool
            .read(Self::cdb_offset(addr), size_of::<u64>() as u64)?
            .try_into()
            .unwrap();
        let cdb = u64::from_le_bytes(bytes);
        if cdb != CDB_FALSE && cdb != CDB_TRUE {
            return Err(Error::InvalidCDB);
        }
        let next_pointer_addr = Self::get_next_pointer_offset(addr, cdb);

        // 4. read the next pointer and check its CRC
        let bytes = mem_pool.read(
            next_pointer_addr,
            size_of::<DurableSingletonListNodeNextPtr>() as u64,
        )?;
        let next_ptr = unsafe { DurableSingletonListNodeNextPtr::from_bytes(&bytes) };
        if !next_ptr.check_crc() {
            return Err(Error::InvalidCRC);
        }

        Ok((node.val, next_ptr.next))
    }

    pub fn read_full_list<M: MemoryPool>(
        &self,
        mem_pool: &M,
        table: &SingletonListTable<N>,
    ) -> Result<Vec<[u8; N]>, Error> {
        if self.head_addr == 0 {
            Ok(Vec::new())
        } else {
            let mut output_vec = Vec::with_capacity(self.len as usize);
            let current_addr = self.head_addr;
            let (val, mut next_addr) = self.read_node_at_addr(mem_pool, table, current_addr)?;
            output_vec.push(val);

            while next_addr != 0 {
                let (val, new_next_addr) = self.read_node_at_addr(mem_pool, table, next_addr)?;
                output_vec.push(val);
                next_addr = new_next_addr;
            }

            Ok(output_vec)
        }
    }
}
