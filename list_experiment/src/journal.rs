// This journal works more like the PMDK log than our verified log.
// Clearing it sets its length to 0 and the head the log is always
// at the same physical address.

use crate::{err::Error, MemoryPool, CDB_FALSE, CDB_TRUE};
use core::mem::size_of;
use crc64fast::Digest;

pub struct Journal {
    start: u64,
    region_size: u64,
    len: u64,
    crc_digest: Digest,
}

impl Journal {
    fn cdb_addr(&self) -> u64 {
        self.start
    }

    fn cdb_false_addr(&self) -> u64 {
        self.start + size_of::<u64>() as u64
    }

    fn cdb_true_addr(&self) -> u64 {
        self.cdb_false_addr() + (size_of::<u64>() * 2) as u64
    }

    fn active_metadata_addr(&self, cdb: u64) -> u64 {
        match cdb {
            CDB_TRUE => self.cdb_true_addr(),
            CDB_FALSE => self.cdb_false_addr(),
            _ => panic!("invalid CDB value"),
        }
    }

    fn inactive_metadata_addr(&self, cdb: u64) -> u64 {
        match cdb {
            CDB_TRUE => self.cdb_false_addr(),
            CDB_FALSE => self.cdb_true_addr(),
            _ => panic!("invalid CDB value"),
        }
    }

    fn log_region_start_addr(&self) -> u64 {
        self.cdb_true_addr() + (size_of::<u64>() * 2) as u64
    }

    fn read_cdb<P: MemoryPool>(&self, mem_pool: &P) -> Result<u64, Error> {
        let bytes = mem_pool.read(self.cdb_addr(), size_of::<u64>() as u64)?;
        let cdb: u64 = u64::from_le_bytes(bytes.try_into().unwrap());
        if cdb != CDB_FALSE && cdb != CDB_TRUE {
            Err(Error::InvalidCDB)
        } else {
            Ok(cdb)
        }
    }

    pub fn setup<P: MemoryPool>(
        mem_pool: &mut P,
        start: u64,
        region_size: u64,
    ) -> Result<Self, Error> {
        if region_size > mem_pool.len() || start + region_size > mem_pool.len() {
            return Err(Error::InvalidMemPoolSize);
        }

        let journal = Self {
            start,
            region_size,
            len: 0,
            crc_digest: Digest::new(),
        };

        let cdb = CDB_FALSE;
        let cdb_bytes = cdb.to_le_bytes();

        let len: u64 = 0;
        let len_bytes = len.to_le_bytes();
        let mut crc_digest = Digest::new();
        crc_digest.write(&len_bytes);
        let crc = crc_digest.sum64();
        let crc_bytes = crc.to_le_bytes();

        let cdb_addr = journal.cdb_addr();
        let metadata_addr = journal.active_metadata_addr(cdb);

        mem_pool.write(cdb_addr, &cdb_bytes)?;
        mem_pool.write(metadata_addr, &len_bytes)?;
        mem_pool.write(metadata_addr + size_of::<u64>() as u64, &crc_bytes)?;

        Ok(journal)
    }

    pub fn append<P: MemoryPool>(
        &mut self,
        mem_pool: &mut P,
        destination: u64,
        bytes: &[u8],
    ) -> Result<(), Error> {
        // sanity check on the memory pool passed in -- is it large enough for the journal?
        if self.region_size > mem_pool.len() || self.start + self.region_size > mem_pool.len() {
            return Err(Error::InvalidMemPoolSize);
        }

        if self.len + bytes.len() as u64 > mem_pool.len() {
            return Err(Error::OutOfSpace);
        }
        let entry_length: u64 = bytes.len() as u64;

        mem_pool.write(
            self.log_region_start_addr() + self.len,
            &entry_length.to_le_bytes(),
        )?;
        mem_pool.write(
            self.log_region_start_addr() + self.len + size_of::<u64>() as u64,
            &destination.to_le_bytes(),
        )?;
        mem_pool.write(
            self.log_region_start_addr() + self.len + (size_of::<u64>() * 2) as u64,
            bytes,
        )?;

        self.crc_digest.write(&entry_length.to_le_bytes());
        self.crc_digest.write(&destination.to_le_bytes());
        self.crc_digest.write(bytes);

        // we update the length in volatile mem here but don't update the
        // durable length field until we commit
        self.len += size_of::<u64>() as u64 * 2 + bytes.len() as u64;

        Ok(())
    }

    pub fn commit<P: MemoryPool>(&mut self, mem_pool: &mut P) -> Result<(), Error> {
        // sanity check on the memory pool passed in -- is it large enough for the journal?
        if self.region_size > mem_pool.len() || self.start + self.region_size > mem_pool.len() {
            return Err(Error::InvalidMemPoolSize);
        }

        if self.len + size_of::<u64>() as u64 > mem_pool.len() {
            return Err(Error::OutOfSpace);
        }

        let crc = self.crc_digest.sum64();
        mem_pool.write(self.log_region_start_addr() + self.len, &crc.to_le_bytes())?;
        mem_pool.flush();
        self.len += size_of::<u64>() as u64;

        // // update the durable length and its crc
        // let len_bytes = self.len.to_le_bytes();
        // let mut crc_digest = Digest::new();
        // crc_digest.write(&len_bytes);
        // let crc = crc_digest.sum64();
        // let crc_bytes = crc.to_le_bytes();

        // let current_cdb = self.read_cdb(mem_pool)?;
        // let inactive_addr = self.inactive_metadata_addr(current_cdb);
        // mem_pool.write(inactive_addr, &len_bytes)?;
        // mem_pool.write(inactive_addr + size_of::<u64>() as u64, &crc_bytes)?;
        // mem_pool.flush();
        // let new_cdb = if current_cdb == CDB_TRUE {
        //     CDB_FALSE
        // } else {
        //     CDB_TRUE
        // };
        // let new_cdb_bytes = new_cdb.to_le_bytes();
        // mem_pool.write(self.cdb_addr(), &new_cdb_bytes)?;
        // mem_pool.flush();
        self.update_inactive_metadata_and_flip_cdb(mem_pool)?;

        Ok(())
    }

    pub fn clear<P: MemoryPool>(&mut self, mem_pool: &mut P) -> Result<(), Error> {
        self.crc_digest = Digest::new();
        self.len = 0;

        self.update_inactive_metadata_and_flip_cdb(mem_pool)?;

        Ok(())
    }

    fn update_inactive_metadata_and_flip_cdb<P: MemoryPool>(
        &self,
        mem_pool: &mut P,
    ) -> Result<(), Error> {
        // update the durable length and its crc
        let len_bytes = self.len.to_le_bytes();
        let mut crc_digest = Digest::new();
        crc_digest.write(&len_bytes);
        let crc = crc_digest.sum64();
        let crc_bytes = crc.to_le_bytes();

        let current_cdb = self.read_cdb(mem_pool)?;
        let inactive_addr = self.inactive_metadata_addr(current_cdb);
        mem_pool.write(inactive_addr, &len_bytes)?;
        mem_pool.write(inactive_addr + size_of::<u64>() as u64, &crc_bytes)?;
        mem_pool.flush();
        let new_cdb = if current_cdb == CDB_TRUE {
            CDB_FALSE
        } else {
            CDB_TRUE
        };
        let new_cdb_bytes = new_cdb.to_le_bytes();
        mem_pool.write(self.cdb_addr(), &new_cdb_bytes)?;
        mem_pool.flush();

        Ok(())
    }
}
