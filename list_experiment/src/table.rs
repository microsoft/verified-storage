use crate::err::Error;

pub const NULL_ADDR: usize = 0;

pub struct TableMetadata {
    start: u64,
    num_rows: u64,
    row_size: u64,
}

impl TableMetadata {
    pub fn new(start: u64, num_rows: u64, row_size: u64) -> Self {
        Self {
            start,
            num_rows,
            row_size,
        }
    }

    pub fn validate_addr(&self, addr: u64) -> bool {
        addr > 0 && self.start <= addr && addr < (self.start + (self.num_rows * self.row_size))
    }

    pub fn row_addr_to_index(&self, addr: u64) -> u64 {
        (addr - self.start) / self.row_size
    }

    pub fn row_index_to_addr(&self, index: u64) -> u64 {
        (index * self.row_size) + self.start
    }
}

// methods for list tables of different durable layouts
pub trait DurableTable {
    fn new(mem_start: u64, mem_size: u64) -> Self;
    fn allocate(&mut self) -> Option<u64>;
    fn free(&mut self, addr: u64) -> Result<(), Error>;
}
