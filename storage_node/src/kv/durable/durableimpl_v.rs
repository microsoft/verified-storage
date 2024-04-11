//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use std::hash::Hash;

verus! {
    pub trait DurableKvStore<PM, K, I, L, E> : Sized
    where
        PM: PersistentMemoryRegions,
        K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
        I: Serializable + Item<K> + Sized + std::fmt::Debug,
        L: Serializable + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> DurableKvStoreView<K, I, L>;

        spec fn recover_to_kv_state(bytes: Seq<Seq<u8>>, id: u128) -> Option<AbstractKvStoreState<K, I, L>>;

        spec fn valid(self) -> bool;

        fn new(pmem: PM,
            kvstore_id: u128,
            max_keys: usize,
            lower_bound_on_max_pages: usize,
        ) -> (result: Result<Self, KvError<K, E>>)
            ensures
                match(result) {
                    Ok(durable_store) => {
                        &&& durable_store@.empty()
                        &&& durable_store.valid()
                    }
                    Err(_) => true // TODO
                };

        fn create(
            &mut self,
            item: I,
            perm: Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(offset) => {
                        &&& self@.len() == old(self)@.len()
                        &&& self@ == old(self)@.create(offset as int, item)
                        &&& 0 <= offset < self@.len()
                        &&& self@[offset as int].is_Some()
                    }
                    Err(_) => true // TODO
                }
        {
            Err(KvError::NotImplemented)
        }

        fn read_item(
            &self,
            offset: u64
        ) -> (result: Option<&I>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(item) => {
                        match self@[offset as int] {
                            Some(entry) => entry.item() == item,
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        ;

        fn read_item_and_list(
            &self,
            offset: u64
        ) -> (result: Option<(&I, &Vec<L>)>)
            requires
                self.valid()
            ensures
                match result {
                    Some((item, pages)) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                &&& entry.item() == item
                                &&& entry.page_entries() == pages@
                            }
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        ;

        fn read_list(
            &self,
            offset: u64
        ) -> (result: Option<&Vec<L>>)
            requires
                self.valid()
            ensures
                match result {
                    Some(pages) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                entry.page_entries() == pages@
                            }
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        ;

        fn update_item(
            &mut self,
            offset: u64,
            new_item: I,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[offset as int], self@[offset as int]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.key() == old_entry.key()
                                &&& entry.item() == new_item
                                &&& entry.pages() == old_entry.pages()
                            }
                            (_, _) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[offset as int].is_None(),
                    Err(_) => true // TODO
                }
        ;

        fn delete(
            &mut self,
            offset: u64,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        self@[offset as int].is_None()
                    }
                    Err(_) => true // TODO
                }
        ;

        fn append(
            &mut self,
            offset: u64,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(phys_offset) => match (old(self)@[offset as int], self@[offset as int]) {
                        (Some(old_entry), Some(entry)) => {
                            entry.pages() == old_entry.pages().push((phys_offset as int, new_entry))
                        }
                        (_, _) => false
                    }
                    Err(_) => true // TODO
                }
        ;

        fn update_item_and_append(
            &mut self,
            offset: u64,
            new_entry: L,
            new_item: I,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(phys_offset) => match (old(self)@[offset as int], self@[offset as int]) {
                        (Some(old_entry), Some(entry)) => {
                            &&& entry.pages() == old_entry.pages().push((phys_offset as int, new_entry))
                            &&& entry.item() == new_item
                        }
                        (_, _) => false
                    }
                    Err(_) => true // TODO
                }
        ;

        fn update_item_at_index(
            &mut self,
            header_offset: u64,
            entry_offset: u64,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => match (old(self)@[header_offset as int], self@[header_offset as int]) {
                        (Some(old), Some(new)) => {
                            let phys_entry_offset = old.pages()[entry_offset as int].0;
                            new.pages() == old.pages().update(entry_offset as int, (phys_entry_offset, new_entry))
                        }
                        (_, _) => false
                    }
                    Err(_) => true // TODO
                }
        ;

        fn update_item_at_index_and_item(
            &mut self,
            offset: u64,
            entry_offset: u64,
            new_item: I,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[offset as int], self@[offset as int]) {
                            (Some(old_entry), Some(entry)) => {
                                let phys_entry_offset = old_entry.pages()[entry_offset as int].0;
                                &&& entry.key() == old_entry.key()
                                &&& entry.item() == new_item
                                &&& entry.pages() == old_entry.pages().update(entry_offset as int, (phys_entry_offset, new_entry))
                            }
                            (_, _) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[offset as int].is_None(),
                    Err(_) => true // TODO
                }
        ;

        fn trim_list(
            &mut self,
            offset: u64,
            new_list_head_offset: u64,
            trim_length: usize, // TODO: make ghost if it's only used in the pre/postconditions
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[offset as int], self@[offset as int]) {
                            (Some(old_entry), Some(entry)) => {
                                entry.pages() == old_entry.pages().subrange(trim_length as int, old_entry.pages().len() as int)
                            }
                            (_,_) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[offset as int].is_None(),
                    Err(_) => true // TODO
                }
        ;

        fn trim_list_and_update_item(
            &mut self,
            offset: u64,
            new_list_head_offset: u64,
            trim_length: usize, // TODO: make ghost if it's only used in the pre/postconditions
            new_item: I,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, Self, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[offset as int], self@[offset as int]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.pages() == old_entry.pages().subrange(trim_length as int, old_entry.pages().len() as int)
                                &&& entry.item() == new_item
                            }
                            (_,_) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[offset as int].is_None(),
                    Err(_) => true // TODO
                }
        ;

    }
}
