#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
    pub trait DurableKvStore<PM, K, H, P, E> : Sized
    where
        PM: PersistentMemoryRegions,
        K: Hash + Eq + Clone + Serializable<E> + Sized + std::fmt::Debug,
        H: Serializable<E> + Header<K> + Sized + std::fmt::Debug,
        P: Serializable<E> + LogicalRange + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> DurableKvStoreView<K, H, P>;

        spec fn recover_to_kv_state(bytes: Seq<Seq<u8>>, id: u128) -> Option<AbstractKvStoreState<K, H, P>>;

        spec fn valid(self) -> bool;

        fn new(pmem: PM,
            kvstore_id: u128,
            max_keys: usize,
            lower_bound_on_max_pages: usize,
            logical_range_gaps_policy: LogicalRangeGapsPolicy
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
            header: H,
            perm: Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                match result {
                    Ok(offset) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                &&& entry.key() == header.spec_key()
                                &&& entry.header() == header
                                &&& entry.pages() == Seq::<(int, P)>::empty()
                            }
                            None => false
                        }
                    }
                    Err(_) => true // TODO
                }
        {
            Err(KvError::NotImplemented)
        }

        fn read_header(
            &self,
            offset: u64
        ) -> (result: Option<&H>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(header) => {
                        match self@[offset as int] {
                            Some(entry) => entry.header() == header,
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        {
            assume(false);
            None
        }

        fn read_header_and_pages(
            &self,
            offset: u64
        ) -> (result: Option<(&H, &Vec<P>)>)
            requires
                self.valid()
            ensures
                match result {
                    Some((header, pages)) => {
                        match self@[offset as int] {
                            Some(entry) => {
                                &&& entry.header() == header
                                &&& entry.page_entries() == pages@
                            }
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        ;

        fn read_pages(
            &self,
            offset: u64
        ) -> (result: Option<&Vec<P>>)
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

        fn update_header(
            &mut self,
            offset: u64,
            new_header: H,
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
                                &&& entry.header() == new_header
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
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>,
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
            new_entry: P,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>
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

        fn update_header_and_append(
            &mut self,
            offset: u64,
            new_entry: P,
            new_header: H,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(phys_offset) => match (old(self)@[offset as int], self@[offset as int]) {
                        (Some(old_entry), Some(entry)) => {
                            &&& entry.pages() == old_entry.pages().push((phys_offset as int, new_entry))
                            &&& entry.header() == new_header
                        }
                        (_, _) => false
                    }
                    Err(_) => true // TODO
                }
        ;

        fn update_page(
            &mut self,
            header_offset: u64,
            entry_offset: u64,
            new_entry: P,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>
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

        fn update_page_and_header(
            &mut self,
            offset: u64,
            entry_offset: u64,
            new_header: H,
            new_entry: P,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>,
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
                                &&& entry.header() == new_header
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
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>,
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

        fn trim_list_and_update_header(
            &mut self,
            offset: u64,
            new_list_head_offset: u64,
            trim_length: usize, // TODO: make ghost if it's only used in the pre/postconditions
            new_header: H,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, H, P, Self, E>>,
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
                                &&& entry.header() == new_header
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
