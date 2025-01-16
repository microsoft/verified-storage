use crate::mem_pool::*;

pub struct MockPool {
    contents: Vec<u8>,
}

impl MockPool {
    pub fn new(size: usize) -> Self {
        Self {
            contents: vec![0; size],
        }
    }
}

impl MemoryPool for MockPool {
    fn len(&self) -> u64 {
        self.contents.len() as u64
    }
}
