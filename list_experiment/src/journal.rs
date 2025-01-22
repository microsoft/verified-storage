// This journal works more like the PMDK log than our verified log.
// Clearing it sets its length to 0 and the head the log is always
// at the same physical address.

use crate::{err::Error, MemoryPool};

pub struct Journal<P: MemoryPool> {
    len: u64,
    mem_pool: P,
}

impl<P: MemoryPool> Journal<P> {
    pub fn new(mem_pool: P) -> Self {
        Self { len: 0, mem_pool }
    }

    // assumes that the mem pool passed in is used only by the journal
    pub fn append(&mut self, bytes: &[u8]) -> Result<(), Error> {
        if self.len + bytes.len() as u64 > self.mem_pool.len() {
            return Err(Error::OutOfSpace);
        }

        self.mem_pool.write(self.len, bytes)?;

        Ok(())
    }

    pub fn clear(&mut self) {
        self.len = 0;
    }
}
