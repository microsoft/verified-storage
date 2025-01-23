use crate::err::Error;
use crate::{DurableTable, PmCopy, TableMetadata};
use core::marker::PhantomData;
use core::mem::size_of;

// stores metadata about each list
pub struct KeyTable<K: PmCopy, M: PmCopy> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
    _key: PhantomData<K>,
    _entry_metadata: PhantomData<M>,
}

impl<K: PmCopy, M: PmCopy> KeyTable<K, M> {
    fn row_size() -> u64 {
        // key, metadata, crc, and cdb
        (size_of::<K>() + size_of::<M>() + size_of::<u64>() * 2) as u64
    }
}

impl<K: PmCopy, M: PmCopy> DurableTable for KeyTable<K, M> {
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = Self::row_size();
        let num_rows = mem_size / row_size;

        let metadata = TableMetadata::new(mem_start, num_rows, row_size);
        let mut free_list = Vec::with_capacity(num_rows as usize);
        for i in 1..num_rows {
            free_list.push(metadata.row_index_to_addr(i));
        }

        Self {
            metadata,
            free_list,
            _key: PhantomData,
            _entry_metadata: PhantomData,
        }
    }

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
}
