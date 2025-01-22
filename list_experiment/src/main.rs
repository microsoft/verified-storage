#![allow(unused_imports)]
use crate::block_list::*;
use crate::list::*;
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

fn main() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_singleton_list_on_mock() {
        let mut mock_pool = MockPool::new(1024);
        let mut list_table: SingletonListTable<8> = SingletonListTable::new(0, mock_pool.len());
        let mut list: DurableSingletonList<8> = DurableSingletonList::new();

        // construct the list
        let mut i: u64 = 0;
        while i < 4 {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        // read the list back in and check that it has the correct values
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == 4);
        for i in 0..4 {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64);
        }
    }

    #[test]
    fn trim_singleton_list_on_mock() {
        let mut mock_pool = MockPool::new(1024);
        let mut list_table: SingletonListTable<8> = SingletonListTable::new(0, mock_pool.len());
        let mut list: DurableSingletonList<8> = DurableSingletonList::new();

        // create the list
        let mut i: u64 = 0;
        while i < 4 {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        // trim the list
        list.trim(&mut mock_pool, &mut list_table, 2).unwrap();

        // check that the list has the correct values
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == 2);
        assert!(u64::from_le_bytes(vec_list[0]) == 2);
        assert!(u64::from_le_bytes(vec_list[1]) == 3);
    }

    #[test]
    fn create_block_list_on_mock() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;

        let mut mock_pool = MockPool::new(1024 * 1024);
        let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
            BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

        let mut i: u64 = 0;
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        // read the list back in and check that it has the correct values
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == list_len as usize);
        for i in 0..list_len as usize {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64);
        }
    }

    #[test]
    fn trim_block_list_on_mock1() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;
        let trim_len = 3;

        let mut mock_pool = MockPool::new(1024 * 1024);
        let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
            BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

        let mut i: u64 = 0;
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        list.trim(&mut mock_pool, &mut list_table, trim_len)
            .unwrap();

        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize);
        for i in 0..vec_list.len() {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }

        // we can append new elements successfully
        let val: u64 = 1;
        let val_bytes = val.to_le_bytes();
        list.append(&mut mock_pool, &mut list_table, val_bytes)
            .unwrap();
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize + 1);
        for i in 0..vec_list.len() - 1 {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }
        assert!(u64::from_le_bytes(vec_list[vec_list.len() - 1]) == 1);
    }

    #[test]
    fn trim_block_list_on_mock2() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;
        let trim_len = 4;

        let mut mock_pool = MockPool::new(1024 * 1024);
        let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
            BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

        let mut i: u64 = 0;
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        list.trim(&mut mock_pool, &mut list_table, trim_len)
            .unwrap();

        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize);
        for i in 0..vec_list.len() {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }

        // we can append new elements successfully
        let val: u64 = 1;
        let val_bytes = val.to_le_bytes();
        list.append(&mut mock_pool, &mut list_table, val_bytes)
            .unwrap();
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize + 1);
        for i in 0..vec_list.len() - 1 {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }
        assert!(u64::from_le_bytes(vec_list[vec_list.len() - 1]) == 1);
    }

    #[test]
    fn trim_block_list_on_mock3() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;
        let trim_len = 7;

        let mut mock_pool = MockPool::new(1024 * 1024);
        let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
            BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

        let mut i: u64 = 0;
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            list.append(&mut mock_pool, &mut list_table, val_bytes)
                .unwrap();
            i += 1;
        }

        list.trim(&mut mock_pool, &mut list_table, trim_len)
            .unwrap();

        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize);
        for i in 0..vec_list.len() {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }
        assert!(vec_list.len() == 0);

        // we can append new elements successfully
        let val: u64 = 1;
        let val_bytes = val.to_le_bytes();
        list.append(&mut mock_pool, &mut list_table, val_bytes)
            .unwrap();
        let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(vec_list.len() == 1);
        assert!(u64::from_le_bytes(vec_list[0]) == 1);
    }
}
