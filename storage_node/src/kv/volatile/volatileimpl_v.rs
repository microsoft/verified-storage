//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::clone::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::hash_map::*; // replace with std::hash_map when available
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {

pub struct VolatileKvIndexEntryImpl
{
    pub header_addr: u64,
    pub list_len: u64,
    pub list_node_addrs: Vec<u64>,
    pub num_list_entries_skipped: u64,
    pub num_list_entries_per_node: Ghost<nat>,
}

impl VolatileKvIndexEntryImpl
{
    pub open spec fn all_locations_in_list_node(&self, list_node_addr: int) -> Seq<VolatileKvListEntryLocation>
    {
        Seq::new(self.num_list_entries_per_node@,
                 |i: int| VolatileKvListEntryLocation{ list_node_addr, offset_within_list_node: i  })
    }

    pub open spec fn entry_locations(&self) -> Seq<VolatileKvListEntryLocation>
    {
        self.list_node_addrs@
            .map(|_i, list_node_addr: u64| self.all_locations_in_list_node(list_node_addr as int))
            .flatten()
            .skip(self.num_list_entries_skipped as int)
    }

    pub open spec fn num_locations(&self) -> int
    {
        self.list_node_addrs.len() * self.num_list_entries_per_node@ - self.num_list_entries_skipped
    }

    pub open spec fn valid(&self) -> bool
    {
        self.list_len <= self.num_locations()
    }

    pub proof fn lemma_num_locations_is_entry_locations_len_helper<T>(s: Seq<Seq<T>>, n: nat)
        requires
            forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() == n,
        ensures
            s.flatten().len() == s.len() * n,
        decreases
            s.len(),
    {
        if s.len() > 0 {
            Self::lemma_num_locations_is_entry_locations_len_helper(s.skip(1), n);
            assert(n + (s.len() - 1) * n == s.len() * n) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(n as int, 1int, s.len() - 1);
            }
        }
    }

    pub proof fn lemma_num_locations_is_entry_locations_len(&self)
        requires
            self.valid()
        ensures
            self.num_locations() == self.entry_locations().len()
    {
        let s = self.list_node_addrs@.map(|_i, list_node_addr: u64|
                                          self.all_locations_in_list_node(list_node_addr as int));
        Self::lemma_num_locations_is_entry_locations_len_helper(s, self.num_list_entries_per_node@);
    }
}

impl View for VolatileKvIndexEntryImpl
{
    type V = VolatileKvIndexEntry;

    open spec fn view(&self) -> Self::V
    {
        VolatileKvIndexEntry {
            header_addr: self.header_addr as int,
            list_len: self.list_len as int,
            entry_locations: self.entry_locations(),
        }
    }
}

impl VolatileKvIndexEntryImpl
{
    pub fn new(header_addr: u64, num_list_entries_per_node: Ghost<nat>) -> (result: Self)
        ensures
            result.valid(),
            result.header_addr == header_addr,
            result.list_len == 0,
            result.list_node_addrs.len() == 0,
            result.num_list_entries_skipped == 0,
            result.num_list_entries_per_node == num_list_entries_per_node,
            result@.valid(),
            result@ == (VolatileKvIndexEntry{
                header_addr: header_addr as int,
                list_len: 0,
                entry_locations: Seq::empty()
            }),
    {
        let result = VolatileKvIndexEntryImpl {
            header_addr,
            list_len: 0,
            list_node_addrs: Vec::<u64>::new(),
            num_list_entries_skipped: 0,
            num_list_entries_per_node,
        };
        assert(result@.entry_locations =~= Seq::empty());
        result
    }
}

#[verifier::reject_recursive_types(K)]
pub struct VolatileKvIndexImpl<K>
where
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
{
    pub m: MyHashMap<K, VolatileKvIndexEntryImpl>,
    pub num_list_entries_per_node: u64,
}

impl<K> VolatileKvIndex<K> for VolatileKvIndexImpl<K>
where
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
{
    open spec fn view(&self) -> VolatileKvIndexView<K>
    {
        VolatileKvIndexView::<K> {
            contents: self.m@.map_values(|v: VolatileKvIndexEntryImpl| v@),
            num_list_entries_per_node: self.num_list_entries_per_node as int
        }
    }

    open spec fn valid(&self) -> bool
    {
        &&& 0 < self.num_list_entries_per_node
        &&& forall |k| #[trigger] self.m@.contains_key(k) ==> self.m@[k].valid()
        &&& forall |k| #[trigger] self.m@.contains_key(k) ==>
            self.m@[k].num_list_entries_per_node@ == self.num_list_entries_per_node
        &&& self.m@.dom().finite()
    }

    fn new(
        kvstore_id: u128,
        max_keys: usize,
        num_list_entries_per_node: u64,
    ) -> (result: Result<Self, KvError<K>>)
    {
        let ret = Self {
            m: MyHashMap::<K, VolatileKvIndexEntryImpl>::new(),
            num_list_entries_per_node
        };
        assert(ret@.contents =~= Map::<K, VolatileKvIndexEntry>::empty());
        Ok(ret)
    }

    fn insert_key(
        &mut self,
        key: &K,
        header_addr: u64,
    ) -> (result: Result<(), KvError<K>>)
    {
        assert(self@.valid()) by {
            self.lemma_valid_implies_view_valid();
        }
        let entry = VolatileKvIndexEntryImpl::new(header_addr, Ghost(self.num_list_entries_per_node as nat));
        let key_clone = key.clone();
        assume(*key == key_clone); // TODO: How do we get Verus to believe this?
        self.m.insert(key_clone, entry);
        assert(self@.contents =~= old(self)@.contents.insert(*key, entry@));
        Ok(())
    }

    // for a new list node addr, adds every location in that node to the volatile index
    fn append_list_node_addr(&mut self, key: &K, list_node_addr: u64) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn append_to_list(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn get(
        &self,
        key: &K
    ) -> (result: Option<u64>)
    {
        match self.m.get(key) {
            Some(entry) => Some(entry.header_addr),
            None => None,
        }
    }

    // Returns the address of the node that contains the list entry at the specified index,
    // as well as which entry in that node corresponds to that list entry.
    fn get_entry_location_by_index(
        &self,
        key: &K,
        idx: usize,
    ) -> (result: Result<(u64, u64), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn remove(
        &mut self,
        key: &K
    ) -> (result: Result<u64, KvError<K>>)
    {
        let result = match self.m.remove(key) {
            Some(entry) => Ok(entry.header_addr),
            None => Err(KvError::<K>::KeyNotFound),
        };
        assert(self@.contents =~= old(self)@.contents.remove(*key));
        result
    }

    // trims the volatile index for the list associated with the key
    fn trim_list(
        &mut self,
        key: &K,
        trim_length: usize
    ) -> (result: Result<(), KvError<K>>)
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    fn get_keys(
        &self
    ) -> (result: Vec<K>)
    {
        assume(false);
        Vec::<K>::new()
    }

    proof fn lemma_valid_implies_view_valid(&self)
    {
        assert forall |k| #[trigger] self@.contains_key(k) implies self@.contents[k].valid() by {
            self.m@[k].lemma_num_locations_is_entry_locations_len();
        }
        assert(self.m@.dom() == self@.contents.dom());
    }
}

}
