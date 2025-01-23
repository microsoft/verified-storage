use crate::{err::Error, mem_pool::*};

pub struct MockPool {
    contents: Vec<u8>,
}

impl MockPool {
    pub fn new(size: u64) -> Self {
        Self {
            contents: vec![0; size as usize],
        }
    }
}

impl MemoryPool for MockPool {
    fn start_addr(&self) -> u64 {
        0
    }

    fn len(&self) -> u64 {
        self.contents.len() as u64
    }

    fn write(&mut self, offset: u64, bytes: &[u8]) -> Result<(), Error> {
        if offset >= self.len() {
            Err(Error::InvalidAddr)
        } else if offset + bytes.len() as u64 > self.len() {
            Err(Error::OutOfBounds)
        } else {
            self.contents[offset as usize..offset as usize + bytes.len()].copy_from_slice(bytes);
            Ok(())
        }
    }

    fn read(&self, offset: u64, len: u64) -> Result<Vec<u8>, Error> {
        if offset >= self.len() {
            Err(Error::InvalidAddr)
        } else if offset + len > self.len() {
            Err(Error::OutOfBounds)
        } else {
            Ok(Vec::from_iter(
                self.contents[offset as usize..(offset + len) as usize]
                    .iter()
                    .cloned(),
            ))
        }
    }

    fn flush(&self) {}
}
