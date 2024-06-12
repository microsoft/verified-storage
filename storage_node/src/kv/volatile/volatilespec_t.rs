//! The `VolatileKvIndex` trait represents the API for the volatile
//! component of a `KvStore`. It maps each key to (1) the address of
//! the metadata header associated with that key, (2) the address of
//! the item associated with that key, and (3) a list of locations of
//! list entries associated with that key. Each such location is
//! the address of a list entry node and an index within that node.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use std::hash::Hash;

verus! {
    pub struct VolatileKvListEntryLocation
    {
        pub list_node_addr: int,
        pub offset_within_list_node: int,
    }
    
    pub struct VolatileKvIndexEntry
    {
        pub header_addr: int,   // the address of the metadata header associated with this key
        pub item_addr: int,     // the address of the item associated with this key
        pub logical_head: int,  // the logical index of the head of the list
        pub logical_tail: int,  // the logical index of the tail of the list
        pub entry_locations: Seq<VolatileKvListEntryLocation>,
                              // the locations of the list entries, starting at the logical head and
                              // extending at least to the tail (and possibly beyond the tail to
                              // reflect free entries)
    }

    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub contents: Map<K, VolatileKvIndexEntry>,
        pub list_entries_per_node: int
    }

    impl<K> VolatileKvIndexView<K>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(self, key: K) -> Option<VolatileKvIndexEntry>
        {
            if self.contents.contains_key(key) {
                Some(self.contents.index(key))
            } else {
                None
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& 0 < self.list_entries_per_node
            &&& forall |k| self.contains_key(k) ==> {
                   let entry = self.contents[k];
                   &&& 0 <= entry.logical_head <= entry.logical_tail
                   &&& entry.entry_locations.len() >= entry.logical_head - entry.logical_tail
               }
        }

        pub open spec fn contains_key(self, key: K) -> bool
        {
            self[key] is Some
        }

        pub open spec fn len(self) -> int
        {
            self.contents.len() as int
        }

        pub open spec fn insert_key(self, key: K, header_addr: int, item_addr: int) -> Self
            recommends
                self.valid(),
                !self.contains_key(key),
        {
            Self {
                contents: self.contents.insert(
                        key,
                        VolatileKvIndexEntry {
                            header_addr,
                            item_addr,
                            logical_head: 0,
                            logical_tail: 0,
                            entry_locations: Seq::empty(),
                        }
                    ),
                ..self
            }
        }

        // adds a new list node's offset to the volatile index. In order to call this, we must have first
        // allocated a new node and inserted an entry into it in the durable store, so we insert
        // the node into the index with `num_entries` set to 1.
        pub open spec fn append_list_node_addr(self, key: K, list_node_addr: int) -> Self
            recommends
                self.valid(),
                self.contains_key(key),
        {
            let entry = self.contents[key];
            let new_locations = Seq::new(self.list_entries_per_node as nat, |i| {
                VolatileKvListEntryLocation {
                    list_node_addr,
                    offset_within_list_node: i,
                }
            });
            Self {
                contents: self.contents.insert(
                    key,
                    VolatileKvIndexEntry {
                        entry_locations: entry.entry_locations + new_locations,
                        ..entry
                    }),
                ..self
            }
        }


        // Returns the address of the list node that contains the specified logical list index,
        // and which entry in that list node corresponds to that logical index.
        pub open spec fn get_list_entry_location<E>(self, key: K, index: int)
                                                    -> Result<VolatileKvListEntryLocation, KvError<K,E>>
            where
                E: std::fmt::Debug
            recommends
                self.valid()
        {
            if !self.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let entry = self.contents[key];
                if index < entry.logical_head || index >= entry.logical_tail {
                    Err(KvError::IndexOutOfRange)
                }
                else {
                    Ok(entry.entry_locations[index - entry.logical_head])
                }
            }
        }

        // returns the length of the list associated with this key
        pub open spec(checked) fn list_len(self, key: K) -> int
            recommends
                self.valid(),
                self.contains_key(key),
        {
            let entry = self.contents[key];
            entry.logical_tail - entry.logical_head
        }

        pub open spec fn key_list_has_free_space(self, key: K) -> bool
            recommends
                self.valid(),
                self.contents.contains_key(key)
        {
            let entry = self.contents[key];
            entry.entry_locations.len() > entry.logical_tail - entry.logical_head
        }

        // Updates the index to reflect that an entry has been appended to the end of the list.
        // It doesn't actually matter what the entry is -- we just need to update the index
        // to reflect that something new has been added
        pub open spec fn append_to_list<E>(self, key: K) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
            recommends
                self.valid(),
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            }
            else {
                let entry = self.contents[key];
                if !self.key_list_has_free_space(key) {
                    Err(KvError::OutOfSpace)
                }
                else {
                    Ok(Self {
                        contents: self.contents.insert(
                            key,
                            VolatileKvIndexEntry {
                                logical_tail: entry.logical_tail + 1,
                                ..entry
                            }),
                        ..self
                    })
                }
            }
        }

        // TODO: clean this up/split into multiple spec functions
        pub open spec fn trim_list<E>(self, key: K, trim_length: int) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
            recommends
                self.valid(),
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let entry = self.contents[key];
                if entry.logical_head > trim_length {
                    Err(KvError::IndexOutOfRange)
                }
                else if entry.logical_tail < trim_length {
                    Err(KvError::IndexOutOfRange)
                }
                else {
                    Ok(Self{
                        contents: self.contents.insert(
                            key,
                            VolatileKvIndexEntry {
                                logical_head: trim_length,
                                entry_locations: entry.entry_locations.skip(trim_length - entry.logical_head),
                                ..entry
                            }),
                        ..self
                    })
                }
            }
        }

        pub closed spec fn remove(self, key: K) -> Self
        {
            Self {
                contents: self.contents.remove(key),
                ..self
            }
        }

        pub open spec fn empty(self) -> bool {
            &&& self.contents.is_empty()
            &&& self.contents.dom().finite()
        }

        pub open spec fn keys(self) -> Set<K> {
            self.contents.dom()
        }
    }

    pub trait VolatileKvIndex<K, E> : Sized
    where
        K: Hash + Eq + Clone + Sized + std::fmt::Debug,
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

        fn insert_key(
            &mut self,
            key: &K,
            header_addr: u64,
            item_addr: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
                old(self)@[*key] is None,
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        &&& self@ == old(self)@.insert_key(*key, header_addr as int, item_addr as int)
                        &&& self@.len() == old(self)@.len() + 1
                    }
                    Err(_) => false // TODO
                }
        ;

        fn append_to_list(
            &mut self,
            key: &K,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
                // The caller has to prove that 1) the key exists and 2) the node we will add to has free
                // space. This function should be called only after a successful durable append,
                // which they can use to prove this.
                old(self)@.contains_key(*key),
                old(self)@.key_list_has_free_space(*key),
            ensures
                self.valid(),
                match (result, old(self)@.append_to_list::<E>(*key)) {
                    (Ok(_), Ok(new_state)) => self@ == new_state,
                    (Err(e1), Err(e2)) => self@ == old(self)@ && e1 == e2,
                    (_, _) => false,
                },
        ;

        fn get(
            &self,
            key: &K
        ) -> (result: Option<u64>)
            requires
                self.valid(),
            ensures
                match (result, self@[*key]) {
                    (Some(addr), Some(entry)) => addr == entry.item_addr,
                    (None, None) => true,
                    (_, _) => false,
                },
        ;

        // Returns the address of the node that contains the list entry at the specified index,
        // as well as which entry in that node corresponds to that list entry.
        fn get_entry_location_by_index(
            &self,
            key: &K,
            idx: usize,
        ) -> (result: Result<(u64, u64), KvError<K, E>>)
            requires
                self.valid(),
            ensures
                match (result, self@.get_list_entry_location::<E>(*key, idx as int)) {
                    (Ok((list_node_addr, offset_within_list_node)), Ok(loc)) => {
                        &&& loc.list_node_addr == list_node_addr
                        &&& loc.offset_within_list_node == offset_within_list_node
                    },
                    (Err(e1), Err(e2)) => e1 == e2,
                    (_, _) => false,
                },
        ;

        fn remove(
            &mut self,
            key: &K
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(_) => self@ == old(self)@.remove(*key),
                    _ => false,
                }
        ;

        // trims the volatile index for the list associated with the key
        fn trim_list(
            &mut self,
            key: &K,
            trim_length: usize
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match (result, old(self)@.trim_list::<E>(*key, trim_length as int)) {
                    (Ok(_), Ok(new_state)) => self@ == new_state,
                    (Err(e1), Err(e2)) => e1 == e2,
                    (_, _) => false,
                },
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
