use crate::block_list::*;
use crate::dll::*;
use crate::journal::*;
use crate::list::*;
use crate::mem_pool::*;
use crate::mock_pool::*;
use crate::singleton_list::*;
use crate::table::*;

#[cfg(test)]
mod tests {

    const POOL_SIZE: u64 = 8192;
    const LIST_TABLE_SIZE: u64 = 4096;
    const KEY_TABLE_SIZE: u64 = 2048;
    const JOURNAL_SIZE: u64 = POOL_SIZE - LIST_TABLE_SIZE - KEY_TABLE_SIZE;
    const CACHE_CAPACITY: u64 = 8;

    use crate::{block_kv::BlockKV, kv::KV, list_cache::ListCache, singleton_kv::SingletonKV};

    use super::*;

    impl PmCopy for u64 {}

    #[test]
    fn create_singleton_list_on_mock() {
        let list_len = 16;

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
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            kv.append(&mut mock_pool, &key, &val_bytes).unwrap();
            i += 1;
        }

        // read the list back in and check that it has the correct values
        let vec_list = kv.read_list(&mut mock_pool, &key).unwrap();

        assert!(vec_list.len() == list_len as usize);
        for i in 0..list_len {
            assert!(u64::from_le_bytes(vec_list[i as usize]) == i as u64);
        }
    }

    #[test]
    fn trim_singleton_list_on_mock() {
        let list_len = 16;

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
        while i < list_len {
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

    #[test]
    fn create_block_list_on_mock() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 20;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
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
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            kv.append(&mut mock_pool, &key, &val_bytes).unwrap();
            i += 1;
        }

        let vec_list = kv.read_list(&mut mock_pool, &key).unwrap();

        assert!(vec_list.len() == list_len as usize);
        for i in 0..list_len {
            assert!(u64::from_le_bytes(vec_list[i as usize]) == i as u64);
        }
    }

    fn block_trim_test_mock_pool<const M: usize>(
        mock_pool: &mut MockPool,
        kv: &mut BlockKV<u64, 8, M>,
        list_len: u64,
        trim_len: u64,
    ) {
        let key = 0;
        kv.insert(mock_pool, &key).unwrap();

        // construct the list
        let mut i: u64 = 0;
        while i < list_len {
            let val_bytes = i.to_le_bytes();
            kv.append(mock_pool, &key, &val_bytes).unwrap();
            i += 1;
        }

        println!("list constructed");

        kv.trim(mock_pool, &key, trim_len).unwrap();

        println!("list trimmed");

        // list can be read and has correct contents
        let vec_list = kv.read_list(mock_pool, &key).unwrap();
        println!("vec list: {:?}", vec_list);
        assert!(vec_list.len() == (list_len - trim_len) as usize);
        for i in 0..vec_list.len() {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }

        println!("list read");

        // we can append new elements successfully
        let val: u64 = 1;
        let val_bytes = val.to_le_bytes();
        kv.append(mock_pool, &key, &val_bytes).unwrap();
        let vec_list = kv.read_list(mock_pool, &key).unwrap();
        assert!(vec_list.len() == (list_len - trim_len) as usize + 1);
        for i in 0..vec_list.len() - 1 {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }
        assert!(u64::from_le_bytes(vec_list[vec_list.len() - 1]) == 1);

        println!("appended to list");
    }

    // trim some but not all nodes from the head
    #[test]
    fn trim_block_list_on_mock1() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;
        let trim_len = 3;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        block_trim_test_mock_pool(&mut mock_pool, &mut kv, list_len, trim_len);
    }

    // trim some nodes from head and some from the next node
    #[test]
    fn trim_block_list_on_mock2() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 7;
        let trim_len = 5;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        block_trim_test_mock_pool(&mut mock_pool, &mut kv, list_len, trim_len);
    }

    // trim multiple full nodes
    #[test]
    fn trim_block_list_on_mock3() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 22;
        let trim_len = 8;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        block_trim_test_mock_pool(&mut mock_pool, &mut kv, list_len, trim_len);
    }

    // trim entire multiple node list
    #[test]
    fn trim_block_list_on_mock4() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 22;
        let trim_len = 22;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        block_trim_test_mock_pool(&mut mock_pool, &mut kv, list_len, trim_len);
    }

    #[test]
    fn trim_and_append_block_list_on_mock() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let list_len = 22;
        let trim_len = 13;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            CACHE_CAPACITY,
        )
        .unwrap();

        block_trim_test_mock_pool(&mut mock_pool, &mut kv, list_len, trim_len);

        let key = 0;
        let old_len: usize = (list_len - trim_len + 1) as usize;

        // append enough additional nodes to trigger allocation
        let append_count: u64 = 8;
        for i in 0..append_count {
            let val_bytes = i.to_le_bytes();
            kv.append(&mut mock_pool, &key, &val_bytes).unwrap();
        }

        let vec_list = kv.read_list(&mock_pool, &key).unwrap();

        for i in 0..vec_list.len() - append_count as usize - 1 {
            assert!(u64::from_le_bytes(vec_list[i]) == i as u64 + trim_len);
        }
        assert!(u64::from_le_bytes(vec_list[old_len - 1]) == 1);
        for i in 0..append_count as usize {
            assert!(u64::from_le_bytes(vec_list[old_len + i]) == i as u64);
        }
    }

    #[test]
    fn cache_evict_block() {
        const ELEMENT_SIZE: usize = 8;
        const ROWS_PER_BLOCK: usize = 4;
        let cache_capacity = 2;

        let mut mock_pool = MockPool::new(POOL_SIZE);
        let mut kv: BlockKV<u64, ELEMENT_SIZE, ROWS_PER_BLOCK> = BlockKV::setup(
            &mut mock_pool,
            KEY_TABLE_SIZE,
            LIST_TABLE_SIZE,
            JOURNAL_SIZE,
            cache_capacity,
        )
        .unwrap();

        // Add more keys than fit in the cache and append to their lists
        let key1 = 1;
        kv.insert(&mut mock_pool, &key1).unwrap();
        kv.append(&mut mock_pool, &key1, &key1.to_le_bytes())
            .unwrap();

        let key2 = 2;
        kv.insert(&mut mock_pool, &key2).unwrap();
        kv.append(&mut mock_pool, &key2, &key2.to_le_bytes())
            .unwrap();

        let key3 = 3;
        kv.insert(&mut mock_pool, &key3).unwrap();
        kv.append(&mut mock_pool, &key3, &key3.to_le_bytes())
            .unwrap();

        // cache contains key2 and key3. we should be able to read key1's list
        let key1_list = kv.read_list(&mock_pool, &key1).unwrap();
        assert!(key1_list == vec![1u64.to_le_bytes()]);

        // cache now contains key1 and key2. we should be able to read key3's list
        let key3_list = kv.read_list(&mock_pool, &key3).unwrap();
        assert!(key3_list == vec![3u64.to_le_bytes()]);

        // cache now contains key1 and key3. we should be able to append to key2's list
        kv.append(&mut mock_pool, &key2, &key2.to_le_bytes())
            .unwrap();
        let key2_list = kv.read_list(&mock_pool, &key2).unwrap();
        assert!(key2_list == vec![2u64.to_le_bytes(); 2]);
    }

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
        let list_cache = ListCache::<8>::new(2);
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
