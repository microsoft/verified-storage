use crc64fast::Digest;

use crate::err::Error;
use crate::{DurableTable, MemoryPool, PmCopy, TableMetadata};
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
    pub fn key_addr(row_addr: u64) -> u64 {
        row_addr
    }

    pub fn metadata_addr(row_addr: u64) -> u64 {
        Self::key_addr(row_addr) + size_of::<K>() as u64
    }

    pub fn crc_addr(row_addr: u64) -> u64 {
        Self::metadata_addr(row_addr) + size_of::<M>() as u64
    }
}

impl<K: PmCopy, M: PmCopy> DurableTable for KeyTable<K, M> {
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = Self::row_size() as u64;
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

    fn row_size() -> usize {
        // key, metadata, crc
        // we aren't including the CDB here because it doesn't
        // come into play with list operations and we aren't implementing
        // recovery right now
        size_of::<K>() + size_of::<M>() + size_of::<u64>()
    }
}

impl<K: PmCopy + Copy, M: PmCopy + Default + Copy> KeyTable<K, M> {
    pub fn insert<P: MemoryPool>(&mut self, mem_pool: &mut P, key: &K) -> Result<u64, Error> {
        // 1. allocate a slot for the new key in the key table
        let new_key_row = match self.allocate() {
            Some(row) => row,
            None => return Err(Error::OutOfSpace),
        };

        // 2. set up the metadata and crc
        let metadata = M::default();

        let mut crc_digest = Digest::new();
        crc_digest.write(key.to_bytes());
        crc_digest.write(metadata.to_bytes());
        let crc = crc_digest.sum64();

        // 3. write them to the entry
        mem_pool.write(KeyTable::<K, M>::key_addr(new_key_row), key.to_bytes())?;
        mem_pool.write(
            KeyTable::<K, M>::metadata_addr(new_key_row),
            metadata.to_bytes(),
        )?;
        mem_pool.write(KeyTable::<K, M>::crc_addr(new_key_row), &crc.to_le_bytes())?;
        mem_pool.flush();

        Ok(new_key_row)
    }

    pub fn read<P: MemoryPool>(&self, mem_pool: &mut P, addr: u64) -> Result<(K, M), Error> {
        // read the entry
        let key_bytes = mem_pool.read(Self::key_addr(addr), size_of::<K>() as u64)?;
        let metadata_bytes = mem_pool.read(Self::metadata_addr(addr), size_of::<M>() as u64)?;
        let crc_bytes = mem_pool.read(Self::crc_addr(addr), size_of::<u64>() as u64)?;

        // check the CRC
        let mut crc_digest = Digest::new();
        crc_digest.write(&key_bytes);
        crc_digest.write(&metadata_bytes);
        let crc = crc_digest.sum64();
        if crc != u64::from_le_bytes(crc_bytes.try_into().unwrap()) {
            return Err(Error::InvalidCRC);
        }

        let key = unsafe { K::from_bytes(&key_bytes) };
        let metadata = unsafe { M::from_bytes(&metadata_bytes) };
        Ok((*key, *metadata))
    }
}
