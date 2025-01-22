#![allow(unused_imports)]
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

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_singleton_list_on_mock() {
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

        // read the list back in and check that it has the correct values
        let head = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(head.is_some());
        let mut current_node = head.as_ref();
        let mut i = 0;
        while current_node.is_some() {
            let node = current_node.unwrap();
            assert!(u64::from_le_bytes(*node.get_val()) == i);
            i += 1;
            current_node = node.next();
        }
        assert!(i == 4);
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
        let head = list.read_full_list(&mock_pool, &list_table).unwrap();
        assert!(head.is_some());
        let mut current_node = head.as_ref();
        let mut i = 2;
        while current_node.is_some() {
            let node: &VolatileSingletonListNode<8> = current_node.unwrap();
            assert!(u64::from_le_bytes(*node.get_val()) == i);
            i += 1;
            current_node = node.next();
        }
        assert!(i == 4);
    }
}
