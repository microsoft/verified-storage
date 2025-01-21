#![allow(unused_imports)]
use crate::mem_pool::*;
use crate::mock_pool::*;
use crate::singleton_list::*;
use crate::table::*;

pub mod block_list;
pub mod err;
pub mod list;
pub mod mem_pool;
pub mod mock_pool;
pub mod singleton_list;
pub mod table;

pub const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
pub const CDB_TRUE: u64 = 0xab21aa73069531b7; // CRC(b"1")

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_singleton_list_on_mock() {
        let mut mock_pool = MockPool::new(64);
        let mut list_table: SingletonListTable<8> = SingletonListTable::new(0, mock_pool.len());
        // let singleton_list = build_volatile_singleton_list_with_len::<8>(15).unwrap();
    }
}
