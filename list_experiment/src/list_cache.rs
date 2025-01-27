use crate::dll::*;
use crate::err::Error;
use crate::PmCopy;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Debug, Clone)]
pub struct ListInfo<const N: usize> {
    index: u64, // helps us remove from the cache map on eviction
    node_addrs: Vec<u64>,
    list_contents: Option<Vec<[u8; N]>>,
}

impl<const N: usize> ListInfo<N> {
    pub fn tail_addr(&self) -> Option<&u64> {
        self.node_addrs.last()
    }

    pub fn push_new_tail_addr(&mut self, new_tail_addr: u64) {
        self.node_addrs.push(new_tail_addr)
    }

    pub fn get_addrs(&self) -> &Vec<u64> {
        &self.node_addrs
    }
}

#[derive(Debug)]
pub struct ListCache<const N: usize> {
    current_size: u64,
    lru_cache: RefCell<DoublyLinkedList<ListInfo<N>>>,
    cache_map: HashMap<u64, usize>,
}

impl<const N: usize> ListCache<N> {
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);
        Self {
            current_size: 0,
            lru_cache: RefCell::new(DoublyLinkedList::new(capacity)),
            cache_map: HashMap::new(),
        }
    }

    pub fn get(&mut self, index: u64) -> Option<ListInfo<N>> {
        let cache_node_index = match self.cache_map.get(&index) {
            Some(node) => *node,
            None => return None,
        };

        // move the node to the head of the list if it isn't already there
        // we don't have to consider the case where the cache does not have
        // a head, because in that case the list is empty and we already
        // returned None.
        let head_index = self.lru_cache.borrow().head_index();
        if let Some(head_index) = head_index {
            if cache_node_index != head_index {
                // remove the node from the cache and pop it onto the front.
                // we don't have to evict anything because the length of the list
                // is unchanged by this operation.
                let node = self.lru_cache.borrow_mut().remove(cache_node_index)?;
                let new_index = self.lru_cache.borrow_mut().push_front(node).unwrap();
                self.cache_map.insert(index, new_index);
            }
        }

        // TODO: ideally would return a reference and not have to clone
        let lru_cache = self.lru_cache.borrow();
        let head = lru_cache.peek_head();
        match head {
            Some(head) => Some((*head).clone()),
            None => None,
        }
    }

    // Updates the tail address at a key index known to be in the cache.
    // `index` is the key table index used for lookups in the cache map,
    // not the index of the cache entry in the internal vector.
    pub fn append_node_addr(&self, index: u64, addr: u64) -> Result<(), Error> {
        let cache_node_index = match self.cache_map.get(&index) {
            Some(node) => *node,
            None => return Err(Error::NotInCache),
        };

        let mut node = self.lru_cache.borrow_mut();
        let list_info = node.get_mut_info_at_index(cache_node_index).unwrap();
        list_info.node_addrs.push(addr);
        Ok(())
    }

    // Trims the cache entry at a key index known to be in the cache.
    pub fn trim(&self, index: u64, trim_len: u64) -> Result<(), Error> {
        let cache_node_index = match self.cache_map.get(&index) {
            Some(node) => *node,
            None => return Err(Error::NotInCache),
        };
        let mut node = self.lru_cache.borrow_mut();
        let list_info = node.get_mut_info_at_index(cache_node_index).unwrap();

        list_info.node_addrs.drain(0..trim_len as usize);
        Ok(())
    }

    // this will only be called when the list at index is not currently
    // in the cache
    pub fn put(&mut self, index: u64, node_addrs: Vec<u64>) {
        let list_info: ListInfo<N> = ListInfo {
            index,
            node_addrs,
            list_contents: None,
        };

        if self.current_size == self.lru_cache.borrow().capacity() as u64 {
            // we need to evict the least recently used entry before inserting the new one
            let evicted_node = self.lru_cache.borrow_mut().pop_back().unwrap();
            let evicted_index = evicted_node.index;
            self.cache_map.remove(&evicted_index);
        } else {
            // current size is less than capacity, so we can insert
            // without evicting. this will increase the current size
            // of the cache
            self.current_size += 1;
        }

        // now we can push the new entry onto the front of the cache list
        let node_ptr = self
            .lru_cache
            .borrow_mut()
            .push_front(Box::new(list_info))
            .unwrap();
        self.cache_map.insert(index, node_ptr);
    }

    pub fn get_tail_addr(&mut self, index: u64) -> Option<u64> {
        let list_info = self.get(index)?;
        let last = list_info.node_addrs.last()?;
        Some(*last)
    }
}
