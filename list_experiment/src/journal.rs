// This journal works more like the PMDK log than our verified log.
// Clearing it sets its length to 0 and the head the log is always
// at the same physical address.

use crate::{err::Error, MemoryPool};
use core::mem::size_of;
use crc64fast::Digest;

pub struct Journal<P: MemoryPool> {
    len: u64,
    mem_pool: P,
    crc_digest: Digest,
}

impl<P: MemoryPool> Journal<P> {
    pub fn new(mem_pool: P) -> Self {
        Self {
            len: 0,
            mem_pool,
            crc_digest: Digest::new(),
        }
    }

    // assumes that the mem pool passed in is used only by the journal
    pub fn append(&mut self, destination: u64, bytes: &[u8]) -> Result<(), Error> {
        if self.len + bytes.len() as u64 > self.mem_pool.len() {
            return Err(Error::OutOfSpace);
        }
        let entry_length: u64 = bytes.len() as u64;

        self.mem_pool.write(self.len, &entry_length.to_le_bytes())?;
        self.mem_pool.write(
            self.len + size_of::<u64>() as u64,
            &destination.to_le_bytes(),
        )?;
        self.mem_pool
            .write(self.len + (size_of::<u64>() * 2) as u64, bytes)?;

        self.crc_digest.write(&entry_length.to_le_bytes());
        self.crc_digest.write(&destination.to_le_bytes());
        self.crc_digest.write(bytes);

        self.len += size_of::<u64>() as u64 * 2 + bytes.len() as u64;

        Ok(())
    }

    // TODO: commit, update length with a cdb on

    pub fn commit(&mut self) -> Result<(), Error> {
        if self.len + size_of::<u64>() as u64 > self.mem_pool.len() {
            return Err(Error::OutOfSpace);
        }

        // TODO: this should also update some metadata stored in the mem pool
        let crc = self.crc_digest.sum64();
        self.mem_pool.write(self.len, &crc.to_le_bytes())?;
        // TODO: mempool flush

        Ok(())
    }

    pub fn clear(&mut self) {
        self.crc_digest = Digest::new();
        self.len = 0;
    }
}
