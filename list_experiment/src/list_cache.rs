use crate::dll::*;
use crate::PmCopy;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Debug)]
pub struct ListInfo<const N: usize> {
    index: u64, // helps us remove from the cache map on eviction
    node_addrs: Vec<u64>,
    list_contents: Option<Vec<[u8; N]>>,
}

#[derive(Debug)]
pub struct ListCache<const N: usize> {
    current_size: u64,
    lru_cache: DoublyLinkedList<ListInfo<N>>,
    cache_map: HashMap<u64, usize>,
}

impl<const N: usize> ListCache<N> {
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);
        Self {
            current_size: 0,
            lru_cache: DoublyLinkedList::new(capacity),
            cache_map: HashMap::new(),
        }
    }

    pub fn get(&mut self, index: u64) -> Option<&ListInfo<N>> {
        let cache_node_index = match self.cache_map.get(&index) {
            Some(node) => *node,
            None => return None,
        };

        // remove the node from the cache and pop it onto the front.
        // we don't have to evict anything because the length of the list
        // is unchanged by this operation.
        let node = self.lru_cache.remove(cache_node_index)?;
        let new_index = self.lru_cache.push_front(node).unwrap();
        self.cache_map.insert(index, new_index);

        self.lru_cache.peek_head()
    }

    // this will only be called when the list at index is not currently
    // in the cache
    pub fn put(&mut self, index: u64, node_addrs: Vec<u64>) {
        let list_info: ListInfo<N> = ListInfo {
            index,
            node_addrs,
            list_contents: None,
        };

        if self.current_size == self.lru_cache.capacity() as u64 {
            // we need to evict the least recently used entry before inserting the new one
            let evicted_node = self.lru_cache.pop_back().unwrap();
            let evicted_index = evicted_node.index;
            self.cache_map.remove(&evicted_index);
        } else {
            // current size is less than capacity, so we can insert
            // without evicting. this will increase the current size
            // of the cache

            self.current_size += 1;
        }

        // now we can push the new entry onto the front of the cache list
        let node_ptr = self.lru_cache.push_front(Box::new(list_info)).unwrap();
        self.cache_map.insert(index, node_ptr);
    }
}
