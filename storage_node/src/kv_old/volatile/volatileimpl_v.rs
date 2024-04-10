//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_t::*;
use std::hash::Hash;

verus! {
    pub trait VolatileKvIndex<K, E> : Sized
    where
        K: Hash + Eq + Clone + Serializable<E> + Sized + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> VolatileKvIndexView<K>;

        spec fn valid(&self) -> bool;

        fn new(
            kvstore_id: u128,
            max_keys: usize,
        ) -> (result: Result<Self, KvError<K, E>>)
            ensures
                match result {
                    Ok(volatile_index) => {
                        &&& volatile_index@.empty()
                        &&& volatile_index.valid()
                    }
                    Err(_) => true // TODO
                }
        ;

        fn insert(
            &mut self,
            key: &K,
            offset: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        &&& self@ == old(self)@.insert_metadata_offset(*key, offset as int)
                    }
                    Err(_) => true // TODO
                }
        ;

        fn append_offset_to_list(
            &mut self,
            key: &K,
            entry_offset: u64
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        self@ == old(self)@.append_entry_offset(*key, entry_offset as int)
                    }
                    Err(_) => true // TODO
                }
        ;

        fn get(
            &self,
            key: &K
        ) -> (result: Option<u64>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(offset) => match self@[*key] {
                            Some(val) => offset == val.metadata_offset,
                            None => false
                        }
                    None => self@[*key].is_None()
                }
        ;

        fn get_entry_location_by_index(
            &self,
            key: &K,
            idx: usize,
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                self.valid(),
            ensures
                match result {
                    Ok(offset) => match self@[*key] {
                        Some(entry) => entry.list_entry_offsets[idx as int] == offset as int,
                        None => false
                    }
                    Err(KvError::KeyNotFound) => !self@.contains_key(*key),
                    Err(KvError::IndexOutOfRange) => match self@[*key] {
                        Some(entry) => idx >= entry.list_entry_offsets.len(),
                        None => false
                    }
                    Err(_) => false
                }
        ;

        fn remove(
            &mut self,
            key: &K
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(offset) => {
                        match old(self)@[*key] {
                            Some(entry) => {
                                &&& entry.metadata_offset == offset as int
                                &&& self@[*key].is_None()
                            }
                            None => false
                        }
                    }
                    Err(_) => true // TODO
                }
        ;

        // trims the volatile index for the list associated with the key
        // and returns the physical offset of the entry that will become the
        // new durable head of the list
        fn trim_list(
            &mut self,
            key: &K,
            trim_length: usize
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(offset) => {
                        match (old(self)@[*key], self@[*key]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.list_entry_offsets ==
                                    old_entry.list_entry_offsets.subrange(
                                        trim_length as int,
                                        old_entry.list_entry_offsets.len() as int
                                    )
                                &&& offset as int == old_entry.list_entry_offsets[trim_length as int]
                            }
                            (_, _) => true // TODO
                        }
                    }
                    Err(_) => true // TODO
                }
        ;

        fn get_keys(
            &self
        ) -> (result: Vec<K>)
            requires
                self.valid(),
            ensures
                self@.keys() == result@.to_set()
        ;

    }
}
