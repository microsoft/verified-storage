use crate::dll::*;
use crate::journal::*;
use crate::journaled_block_list::*;
use crate::journaled_singleton_list::*;
use crate::list::*;
use crate::mem_pool::*;
use crate::mock_pool::*;
use crate::table::*;

#[cfg(test)]
mod tests {

    const POOL_SIZE: u64 = 4096;
    const LIST_TABLE_SIZE: u64 = 2048;
    const KEY_TABLE_SIZE: u64 = 1024;
    const JOURNAL_SIZE: u64 = POOL_SIZE - LIST_TABLE_SIZE - KEY_TABLE_SIZE;
    const CACHE_CAPACITY: u64 = 8;

    use crate::{kv::KV, list_cache::ListCache, singleton_kv::SingletonKV};

    use super::*;

    impl PmCopy for u64 {}

    #[test]
    fn create_singleton_list_on_mock() {
        let kv_entries = 16;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: SingletonKV<u64, 8> = SingletonKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        let key = 0;
        kv.insert(&mut mock_pool, &key).unwrap();

        // construct the list
        let mut i: u64 = 0;
        while i < kv_entries {
            let val_bytes = i.to_le_bytes();
            kv.append(&mut mock_pool, &key, &val_bytes).unwrap();
            i += 1;
        }

        // read the list back in and check that it has the correct values
        let vec_list = kv.read_list(&mut mock_pool, &key).unwrap();

        assert!(vec_list.len() == kv_entries as usize);
        for i in 0..kv_entries {
            assert!(u64::from_le_bytes(vec_list[i as usize]) == i as u64);
        }
    }

    #[test]
    fn trim_singleton_list_on_mock() {
        let kv_entries = 16;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: SingletonKV<u64, 8> = SingletonKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        let key = 0;
        kv.insert(&mut mock_pool, &key).unwrap();

        // construct the list
        let mut i: u64 = 0;
        while i < kv_entries {
            let val_bytes = i.to_le_bytes();
            kv.append(&mut mock_pool, &key, &val_bytes).unwrap();
            i += 1;
        }

        // trim the list
        kv.trim(&mut mock_pool, &key, 2).unwrap();

        // check that the list has the correct values
        let vec_list = kv.read_list(&mock_pool, &key).unwrap();
        assert!(vec_list.len() == 14);
        let mut i: u64 = 2;
        for val in &vec_list {
            let val_bytes = i.to_le_bytes();
            assert!(val_bytes == *val);
            i += 1;
        }
    }

    // #[test]
    // fn create_block_list_on_mock() {
    //     const ELEMENT_SIZE: usize = 8;
    //     const ROWS_PER_BLOCK: usize = 4;
    //     let list_len = 7;

    //     let mut mock_pool = MockPool::new(POOL_SIZE);
    //     let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
    //         BlockListTable::new(0, LIST_TABLE_SIZE);
    //     let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

    //     let mut journal = Journal::setup(&mut mock_pool, LIST_TABLE_SIZE, JOURNAL_SIZE).unwrap();

    //     let mut i: u64 = 0;
    //     while i < list_len {
    //         let val_bytes = i.to_le_bytes();
    //         list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //             .unwrap();
    //         i += 1;
    //     }

    //     // read the list back in and check that it has the correct values
    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == list_len as usize);
    //     for i in 0..list_len as usize {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64);
    //     }
    // }

    // #[test]
    // fn trim_block_list_on_mock1() {
    //     const ELEMENT_SIZE: usize = 8;
    //     const ROWS_PER_BLOCK: usize = 4;
    //     let list_len = 7;
    //     let trim_len = 3;

    //     let mut mock_pool = MockPool::new(POOL_SIZE);
    //     let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
    //         BlockListTable::new(0, LIST_TABLE_SIZE);
    //     let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

    //     let mut journal = Journal::setup(&mut mock_pool, LIST_TABLE_SIZE, JOURNAL_SIZE).unwrap();

    //     let mut i: u64 = 0;
    //     while i < list_len {
    //         let val_bytes = i.to_le_bytes();
    //         list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //             .unwrap();
    //         i += 1;
    //     }

    //     list.trim(&mut mock_pool, &mut list_table, trim_len)
    //         .unwrap();

    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == (list_len - trim_len) as usize);
    //     for i in 0..vec_list.len() {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
    //     }

    //     // we can append new elements successfully
    //     let val: u64 = 1;
    //     let val_bytes = val.to_le_bytes();
    //     list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //         .unwrap();
    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == (list_len - trim_len) as usize + 1);
    //     for i in 0..vec_list.len() - 1 {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
    //     }
    //     assert!(u64::from_le_bytes(vec_list[vec_list.len() - 1]) == 1);
    // }

    // #[test]
    // fn trim_block_list_on_mock2() {
    //     const ELEMENT_SIZE: usize = 8;
    //     const ROWS_PER_BLOCK: usize = 4;
    //     let list_len = 7;
    //     let trim_len = 4;

    //     let mut mock_pool = MockPool::new(POOL_SIZE);
    //     let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
    //         BlockListTable::new(0, LIST_TABLE_SIZE);
    //     let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

    //     let mut journal = Journal::setup(&mut mock_pool, LIST_TABLE_SIZE, JOURNAL_SIZE).unwrap();

    //     let mut i: u64 = 0;
    //     while i < list_len {
    //         let val_bytes = i.to_le_bytes();
    //         list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //             .unwrap();
    //         i += 1;
    //     }

    //     list.trim(&mut mock_pool, &mut list_table, trim_len)
    //         .unwrap();

    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == (list_len - trim_len) as usize);
    //     for i in 0..vec_list.len() {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
    //     }

    //     // we can append new elements successfully
    //     let val: u64 = 1;
    //     let val_bytes = val.to_le_bytes();
    //     list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //         .unwrap();
    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == (list_len - trim_len) as usize + 1);
    //     for i in 0..vec_list.len() - 1 {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
    //     }
    //     assert!(u64::from_le_bytes(vec_list[vec_list.len() - 1]) == 1);
    // }

    // #[test]
    // fn trim_block_list_on_mock3() {
    //     const ELEMENT_SIZE: usize = 8;
    //     const ROWS_PER_BLOCK: usize = 4;
    //     let list_len = 7;
    //     let trim_len = 7;

    //     let mut mock_pool = MockPool::new(POOL_SIZE);
    //     let mut list_table: BlockListTable<ELEMENT_SIZE, ROWS_PER_BLOCK> =
    //         BlockListTable::new(0, LIST_TABLE_SIZE);
    //     let mut list: DurableBlockList<ELEMENT_SIZE, ROWS_PER_BLOCK> = DurableBlockList::new();

    //     let mut journal = Journal::setup(&mut mock_pool, LIST_TABLE_SIZE, JOURNAL_SIZE).unwrap();

    //     let mut i: u64 = 0;
    //     while i < list_len {
    //         let val_bytes = i.to_le_bytes();
    //         list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //             .unwrap();
    //         i += 1;
    //     }

    //     list.trim(&mut mock_pool, &mut list_table, trim_len)
    //         .unwrap();

    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == (list_len - trim_len) as usize);
    //     for i in 0..vec_list.len() {
    //         assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
    //     }
    //     assert!(vec_list.len() == 0);

    //     // we can append new elements successfully
    //     let val: u64 = 1;
    //     let val_bytes = val.to_le_bytes();
    //     list.append(&mut mock_pool, &mut list_table, &mut journal, &val_bytes)
    //         .unwrap();
    //     let vec_list = list.read_full_list(&mock_pool, &list_table).unwrap();
    //     assert!(vec_list.len() == 1);
    //     assert!(u64::from_le_bytes(vec_list[0]) == 1);
    // }

    #[test]
    fn dll1() {
        let num_nodes: usize = 64;
        let mut dll = DoublyLinkedList::<u64>::new(num_nodes);

        for i in 0..num_nodes {
            let _ = dll.push_front(Box::new(i.try_into().unwrap()));
        }

        for i in 0..num_nodes {
            let node = dll.pop_back();

            assert!(node.is_some());
            assert!(*node.unwrap() == i.try_into().unwrap());
        }
    }

    #[test]
    fn dll2() {
        let num_nodes: usize = 64;
        let mut dll = DoublyLinkedList::<u64>::new(num_nodes);
        let mut node_vec = Vec::new();

        for i in 0..num_nodes {
            let node_ptr = dll.push_front(Box::new(i.try_into().unwrap()));
            node_vec.push(node_ptr);
        }

        // random node from the interior of the list
        let node_to_remove = node_vec[13].unwrap();
        let node = dll.remove(node_to_remove).unwrap();
        assert!(*node == 13);

        let mut i = 0;
        while !dll.is_empty() {
            let node = dll.pop_back();
            assert!(node.is_some());
            let val = *node.unwrap();
            assert!(val != 13);
            assert!(val == i);

            i += 1;
            if i == 13 {
                i += 1;
            }
        }
    }

    #[test]
    fn lru1() {
        let mut list_cache = ListCache::<8>::new(2);
        let index0 = 0;
        let index1 = 1;
        let index2 = 2;

        let node_addrs = Vec::new();

        list_cache.put(index0, node_addrs.clone());
        list_cache.put(index1, node_addrs.clone());
        list_cache.put(index2, node_addrs.clone());

        // index0 should have been evicted
        assert!(list_cache.get(index0).is_none());

        // index1 is most recently accessed
        list_cache.get(index1);
        // inserting index0 should evict index2
        list_cache.put(index0, node_addrs.clone());

        assert!(list_cache.get(index0).is_some());
        assert!(list_cache.get(index2).is_none());
    }
}
