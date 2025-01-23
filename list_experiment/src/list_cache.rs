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
    capacity: u64,
    current_size: u64,
    lru_cache: DoublyLinkedList<ListInfo<N>>,
    cache_map: HashMap<u64, *mut DoublyLinkedListNode<ListInfo<N>>>,
}

impl<const N: usize> ListCache<N> {
    pub fn new(capacity: u64) -> Self {
        assert!(capacity > 0);
        Self {
            capacity,
            current_size: 0,
            lru_cache: DoublyLinkedList::new(),
            cache_map: HashMap::new(),
        }
    }

    pub fn get(&mut self, index: u64) -> Option<&ListInfo<N>> {
        let cache_node = match self.cache_map.get(&index) {
            Some(node) => *node,
            None => return None,
        };
        let node = unsafe { &*cache_node };
        let list_info = node.get_value();

        // remove the node from the cache and pop it onto the front.
        // we don't have to evict anything because the length of the list
        // is unchanged by this operation.
        let cache_node = self.lru_cache.remove(cache_node);
        self.lru_cache.push_front(cache_node);

        // we don't have to update the cache map because it still points to the correct
        // node (i think)

        Some(&list_info)
    }

    // this will only be called when the list at index is not currently
    // in the cache
    pub fn put(&mut self, index: u64, node_addrs: Vec<u64>) {
        let list_info: ListInfo<N> = ListInfo {
            index,
            node_addrs,
            list_contents: None,
        };
        let new_node = DoublyLinkedListNode::new(list_info);

        if self.current_size == self.capacity {
            // we need to evict the least recently used entry before inserting the new one
            let evicted_node = self.lru_cache.pop_back().unwrap();
            let evicted_index = evicted_node.get_value().index;
            self.cache_map.remove(&evicted_index);
        } else {
            // current size is less than capacity, so we can insert
            // without evicting. this will increase the current size
            // of the cache

            self.current_size += 1;
        }

        // now we can push the new entry onto the front of the cache list
        let node_ptr = self.lru_cache.push_front(Box::new(new_node));
        self.cache_map.insert(index, node_ptr);
    }
}
