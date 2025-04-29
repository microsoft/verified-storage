//! A `VolatileKvIndex` represents the volatile component of a `KvStore`.
//! Currently, it maps each key to 1) the physical offset of the metadata header associated
//! with that key in the header store, and 2) a list of physical offsets of list entries
//! associated with that key.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {

pub struct VolatileKvListEntryLocation
{
    pub list_node_addr: int,
    pub offset_within_list_node: int,
}

pub struct VolatileKvIndexEntry
{
    pub header_addr: u64,   // the address of the metadata header associated with this key
    pub list_len: int,      // the length of the list
    pub entry_locations: Seq<VolatileKvListEntryLocation>,
                          // the locations of the list entries, possibly including extra
                          // beyond the tail to reflect free entries
}

impl VolatileKvIndexEntry
{
    pub open spec fn valid(&self) -> bool
    {
        0 <= self.list_len <= self.entry_locations.len()
    }
}

#[verifier::reject_recursive_types(K)]
pub struct VolatileKvIndexView<K>
where
    K: PmCopy + Hash,
{
    pub contents: Map<K, VolatileKvIndexEntry>,
    pub num_list_entries_per_node: int
}

impl<K> VolatileKvIndexView<K>
where
    K: PmCopy + Hash + std::fmt::Debug,
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
        &&& 0 < self.num_list_entries_per_node
        &&& forall |k| #[trigger] self.contains_key(k) ==> self.contents[k].valid()
    }

    pub open spec fn contains_key(self, key: K) -> bool
    {
        self[key] is Some
    }

    pub open spec fn insert_key(self, key: K, header_addr: u64) -> Self
        recommends
            self.valid(),
            !self.contains_key(key),
    {
        Self {
            contents: self.contents.insert(
                    key,
                    VolatileKvIndexEntry {
                        header_addr,
                        list_len: 0,
                        entry_locations: Seq::empty(),
                    }
                ),
            ..self
        }
    }

    // for a new list node addr, adds every location in that node to the volatile index
    pub open spec fn append_list_node_addr(self, key: K, list_node_addr: int) -> Self
        recommends
            self.valid(),
            self.contains_key(key),
    {
        let entry = self.contents[key];
        let new_locations = Seq::new(self.num_list_entries_per_node as nat, |i| {
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
    pub open spec fn get_list_entry_location(self, key: K, index: int)
                                             -> Result<VolatileKvListEntryLocation, KvError<K>>
        recommends
            self.valid()
    {
        if !self.contains_key(key) {
            Err(KvError::KeyNotFound)
        } else {
            let entry = self.contents[key];
            if index < 0 || index >= entry.entry_locations.len() {
                Err(KvError::IndexOutOfRange)
            }
            else {
                Ok(entry.entry_locations[index])
            }
        }
    }

    // returns the length of the list associated with this key
    pub open spec(checked) fn list_len(self, key: K) -> int
        recommends
            self.valid(),
            self.contains_key(key),
    {
        self.contents[key].list_len
    }

    pub open spec fn key_list_has_free_space(self, key: K) -> bool
        recommends
            self.valid(),
            self.contents.contains_key(key)
    {
        let entry = self.contents[key];
        entry.entry_locations.len() > entry.list_len
    }

    // Updates the index to reflect that an entry has been appended to the end of the list.
    // It doesn't actually matter what the entry is -- we just need to update the index
    // to reflect that something new has been added
    pub open spec fn append_to_list(self, key: K) -> Result<Self, KvError<K>>
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
                            list_len: entry.list_len + 1,
                            ..entry
                        }),
                    ..self
                })
            }
        }
    }

    // TODO: clean this up/split into multiple spec functions
    pub open spec fn trim_list(self, key: K, trim_length: int) -> Result<Self, KvError<K>>
        recommends
            self.valid(),
    {
        if !self.contents.contains_key(key) {
            Err(KvError::KeyNotFound)
        } else {
            let entry = self.contents[key];
            if trim_length < 0 {
                Err(KvError::IndexOutOfRange)
            }
            else if entry.list_len < trim_length {
                Err(KvError::IndexOutOfRange)
            }
            else {
                Ok(Self{
                    contents: self.contents.insert(
                        key,
                        VolatileKvIndexEntry {
                            list_len: entry.list_len - trim_length,
                            entry_locations: entry.entry_locations.skip(trim_length),
                            ..entry
                        }),
                    ..self
                })
            }
        }
    }

    pub open spec fn remove(self, key: K) -> Self
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

pub trait VolatileKvIndex<K> : Sized
where
    K: PmCopy + Hash + Clone + Sized + std::fmt::Debug,
{
    spec fn view(&self) -> VolatileKvIndexView<K>;

    spec fn tentative_view(&self) -> VolatileKvIndexView<K>;

    spec fn valid(&self) -> bool;

    spec fn num_tentative_entries(self) -> nat;

    fn new(
        kvstore_id: u128,
        max_keys: usize,
        num_list_entries_per_node: u64,
    ) -> (result: Result<Self, KvError<K>>)
        requires
            num_list_entries_per_node > 0,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures
            match result {
                Ok(volatile_index) => {
                    &&& volatile_index@.empty()
                    &&& volatile_index.tentative_view().empty()
                    &&& volatile_index.valid()
                    &&& volatile_index.num_tentative_entries() == 0
                },
                Err(_) => false,
            }
    ;

    // This function inserts a key directly into the non-tentative
    // index and is only used during startup when filling in the 
    // index with existing records
    fn insert_key_during_startup(
        &mut self,
        key: &K,
        header_addr: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            old(self)@[*key] is None,
            old(self).tentative_view() == old(self)@,
            old(self).num_tentative_entries() == 0,
        ensures
            self.valid(),
            self.tentative_view() == old(self).tentative_view().insert_key(*key, header_addr),
            self.num_tentative_entries() == 0,
            match result {
                Ok(()) => self@ == old(self)@.insert_key(*key, header_addr),
                Err(_) => false, // TODO
            }
    ;


    fn insert_key(
        &mut self,
        key: &K,
        header_addr: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            old(self).tentative_view()[*key] is None,
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self.tentative_view() == old(self).tentative_view().insert_key(*key, header_addr)
                    &&& self@ == old(self)@
                    &&& self.num_tentative_entries() > 0
                }
                Err(_) => false, // TODO
            }
    ;

    // for a new list node addr, adds every location in that node to the volatile index
    fn append_list_node_addr(&mut self, key: &K, list_node_addr: u64) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            old(self)@.contains_key(*key),
        ensures
            self.valid(),
            match result { 
                Ok(_) => self@ == old(self)@.append_list_node_addr(*key, list_node_addr as int),
                Err(_) => false,
            },
    ;

    fn append_to_list(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            // The caller has to prove that 1) the key exists and 2) the node we will add to has free
            // space. This function should be called only after a successful durable append,
            // which they can use to prove this.
            old(self)@.contains_key(*key),
            old(self)@.key_list_has_free_space(*key),
        ensures
            self.valid(),
            match (result, old(self)@.append_to_list(*key)) {
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
            match (result, self.tentative_view()[*key]) {
                (Some(addr), Some(entry)) => addr == entry.header_addr,
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
    ) -> (result: Result<(u64, u64), KvError<K>>)
        requires
            self.valid(),
        ensures
            match (result, self@.get_list_entry_location(*key, idx as int)) {
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
    ) -> (result: Result<u64, KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(header_addr) => {
                    &&& self@ == old(self)@
                    &&& old(self).tentative_view().contains_key(*key)
                    &&& self.tentative_view() == old(self).tentative_view().remove(*key)
                    &&& header_addr == old(self).tentative_view()[*key].unwrap().header_addr
                },
                Err(KvError::KeyNotFound) => {
                    &&& self == old(self)
                    &&& !old(self).tentative_view().contains_key(*key)
                }
                _ => false,
            }
    ;

    // trims the volatile index for the list associated with the key
    fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match (result, old(self)@.trim_list(*key, trim_length as int)) {
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
