//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::clone::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_v::*;
use crate::pmem::pmcopy_t::*;
use std::collections::HashMap;
use std::hash::Hash;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

#[derive(Clone)]
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
            header_addr: self.header_addr,
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
                header_addr: header_addr,
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

pub enum PendingIndexEntry {
    Created(VolatileKvIndexEntryImpl),
    ReplaceExisting(VolatileKvIndexEntryImpl),
    Deleted,
}

// pub struct PendingIndexEntry {
//     pub status: EntryStatus,
//     pub entry: VolatileKvIndexEntryImpl
// }

// impl PendingIndexEntry {
//     pub open spec fn view(self) -> VolatileKvIndexEntry 
//     {
//         self.entry@
//     }
// }

#[verifier::reject_recursive_types(K)]
pub struct VolatileKvIndexImpl<K>
where
    K: PmCopy + Hash + Eq + KeyEq + Clone + Sized + std::fmt::Debug,
{
    pub m: HashMap<K, VolatileKvIndexEntryImpl>,
    pub tentative: HashMap<K, PendingIndexEntry>, // TODO prob need to differentiate deleted vs created?
    pub tentative_keys: Vec<K>,
    pub num_list_entries_per_node: u64,
}

impl<K> VolatileKvIndex<K> for VolatileKvIndexImpl<K>
where
    K: PmCopy + Hash + Eq + KeyEq + Clone + Sized + std::fmt::Debug,
{
    open spec fn view(&self) -> VolatileKvIndexView<K>
    {
        VolatileKvIndexView::<K> {
            contents: self.m@.map_values(|v: VolatileKvIndexEntryImpl| v@),
            num_list_entries_per_node: self.num_list_entries_per_node as int
        }
    }

    open spec fn num_tentative_entries(self) -> nat {
        self.tentative_keys@.len()
    }

    open spec fn tentative_view(&self) -> VolatileKvIndexView<K>
    {
        let outstanding_keys_to_add = self.tentative@.dom().filter(
            |k| self.tentative@[k] is Created 
        );
        let outstanding_keys_to_delete = self.tentative@.dom().filter(
            |k| self.tentative@[k] is Deleted
        );
        let keys = self.m@.dom().union(outstanding_keys_to_add) - outstanding_keys_to_delete;
        VolatileKvIndexView::<K> {
            contents: Map::new(
                |k| keys.contains(k),
                |k| if self.tentative@.contains_key(k) {
                        match self.tentative@[k] {
                            PendingIndexEntry::Created(entry) | PendingIndexEntry::ReplaceExisting(entry) => entry@,
                            _ => arbitrary() // this can't happen, but we have to return something
                        }
                    } else {
                        self.m@[k]@
                    }
            ),
            num_list_entries_per_node: self.num_list_entries_per_node as int
        }
    }

    open spec fn valid(&self) -> bool
    {
        &&& 0 < self.num_list_entries_per_node
        &&& self.tentative@.dom().finite()
        &&& forall |k| #[trigger] self.m@.contains_key(k) ==> self.m@[k].valid()
        &&& forall |k| #[trigger] self.m@.contains_key(k) ==>
            self.m@[k].num_list_entries_per_node@ == self.num_list_entries_per_node
        &&& vstd::std_specs::hash::obeys_key_model::<K>()
        // does this one matter?
        // // the tentative version of an entry is not the same as the committed version
        // &&& forall |k| #[trigger] self@.contents.contains_key(k) && self.tentative@.contains_key(k) ==>
        //         self@.contents[k] != self.tentative@[k]@
        &&& self.tentative@.dom() == self.tentative_keys@.to_set()
        &&& self.tentative_keys@.no_duplicates()
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
            ||| self.tentative@[k] is Created 
            ||| self.tentative@[k] is Deleted
            ||| self.tentative@[k] is ReplaceExisting
        }
        // if a key was deleted (but not created) in the current transaction,
        // it must already exist
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k] is Deleted ==>
                self.m@.contains_key(k)
        // if a key was created in this transaction, it must not already exist
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k] is Created ==>
                !self.m@.contains_key(k)
        // if we've done operations that replace an existing index entry for a key with 
        // a new one, that key must already exist in the index
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k] is ReplaceExisting ==>
                self.m@.contains_key(k)
        // all entries pending create are valid
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
            &&& self.tentative@[k] is Created ==> {
                &&& self.tentative@[k] matches PendingIndexEntry::Created(entry)
                &&& entry.valid()
                &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
            }
            &&& self.tentative@[k] is ReplaceExisting ==> {
                &&& self.tentative@[k] matches PendingIndexEntry::ReplaceExisting(entry)
                &&& entry.valid()
                &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
            }
        }
            
    }

    fn new(
        kvstore_id: u128,
        max_keys: usize,
        num_list_entries_per_node: u64,
    ) -> (result: Result<Self, KvError<K>>)
    {
        let ret = Self {
            m: HashMap::<K, VolatileKvIndexEntryImpl>::new(),
            tentative: HashMap::<K, PendingIndexEntry>::new(),
            tentative_keys: Vec::new(),
            num_list_entries_per_node
        };
        assert(ret@.contents =~= Map::<K, VolatileKvIndexEntry>::empty());
        assert(ret.tentative@ =~= Map::<K, PendingIndexEntry>::empty());
        assert(ret.tentative_keys@ == Seq::<K>::empty());
        assert(ret.tentative@.dom() == ret.tentative_keys@.to_set());
        assert(ret.tentative_view().empty()) by {
            assert(ret.tentative_view().contents.dom() == ret.m@.dom().union(ret.tentative@.dom()));
        }
        Ok(ret)
    }

    fn insert_key_during_startup(
        &mut self,
        key: &K,
        header_addr: u64,
    ) -> (result: Result<(), KvError<K>>)
    {
        assert(self@.valid()) by {
            self.lemma_valid_implies_view_valid();
        }
        let entry = VolatileKvIndexEntryImpl::new(header_addr, Ghost(self.num_list_entries_per_node as nat));
        let key_clone = key.clone_provable();
        self.m.insert(key_clone, entry);

        proof {
            assert(self@.contents =~= old(self)@.contents.insert(*key, entry@));
            self.lemma_if_no_tentative_entries_then_tentative_view_matches_view();
            assert(self.tentative_view() == self@); 
            assert(self.tentative_view() == old(self).tentative_view().insert_key(*key, header_addr));
        }

        Ok(())
    }

    // This function is intended to be used during a transaction and inserts
    // the key into the tentative map
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
        let key_clone = key.clone_provable();
        let key_clone2 = key.clone_provable();

        // the type of the pending entry depends on whether the key already exists
        // in the main index or not.
        // if it doesn't exist in the main index, we're creating a new entry.
        // if it does, we've presumably deleted and re-created the key in this
        // transaction, so we use the ReplaceExisting variant
        let new_entry = if self.m.get(key).is_none() {
            PendingIndexEntry::Created(entry)
        } else {
            PendingIndexEntry::ReplaceExisting(entry)
        };
        
        if !self.tentative.contains_key(key) {
            assert(!self.tentative_keys@.contains(*key));
            // we only add the key to tentative_keys if it's not already in there
            self.tentative_keys.push(key_clone2);
            assert(self.tentative_keys@ == old(self).tentative_keys@.push(*key));
            assert(self.tentative_keys@[self.tentative_keys@.len() - 1] == *key);
            assert(self.tentative_keys@.subrange(0, old(self).tentative_keys@.len() as int) == old(self).tentative_keys@);
        } else {
            assert(self.tentative_keys@.contains(*key));
        }

        self.tentative.insert(key_clone, new_entry);
        
        assert(self.tentative_view().contents =~= 
            old(self).tentative_view().insert_key(*key, header_addr).contents);

        assert(self.tentative@.dom() == self.tentative_keys@.to_set());

        assert(self.tentative_keys@.no_duplicates());

        assert(forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
            ||| self.tentative@[k] is Created 
            ||| self.tentative@[k] is Deleted
            ||| self.tentative@[k] is ReplaceExisting
        });

        assert(forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k] is Deleted ==>
            self.m@.contains_key(k));
        
        assert(forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
            &&& self.tentative@[k] is Created ==> {
                &&& self.tentative@[k] matches PendingIndexEntry::Created(entry)
                &&& entry.valid()
                &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
            }
            &&& self.tentative@[k] is ReplaceExisting ==> {
                &&& self.tentative@[k] matches PendingIndexEntry::ReplaceExisting(entry)
                &&& entry.valid()
                &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
            }
        });

        assert(self.valid());

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
        match self.tentative.get(key) {
            Some(entry) => {
                match entry {
                    PendingIndexEntry::Created(entry) | PendingIndexEntry::ReplaceExisting(entry) => 
                        Some(entry.header_addr),
                    PendingIndexEntry::Deleted => None,
                }
            }
            None => {
                match self.m.get(key) {
                    Some(entry) => Some(entry.header_addr),
                    None => None,
                }
            }
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
        
        assert(self@.valid()) by {
            self.lemma_valid_implies_view_valid();
        }

        broadcast use vstd::std_specs::hash::group_hash_axioms;

        if self.tentative.contains_key(key) {
            let entry = self.tentative.get(key).unwrap();
            match entry {
                PendingIndexEntry::Created(entry) => {
                    let header_addr = entry.header_addr;
                    // The key has been tentatively created. It doesn't 
                    // exist durably yet, so we'll just remove it from
                    // the tentative list
                    
                    // also find the index of the key we want to remove.
                    // it's easier to remove the key outside of the loop.
                    let mut i = 0;
                    while i < self.tentative_keys.len()
                        invariant
                            old(self).tentative_keys@ == self.tentative_keys@,
                            forall |j: int| 0 <= j < i ==> self.tentative_keys@[j] != *key,
                        ensures 
                            ({
                                ||| i >= self.tentative_keys@.len()
                                ||| self.tentative_keys@[i as int] == key
                            })
                    {
                        let current_key = &self.tentative_keys[i];
                        if current_key.key_eq(key) {
                            assert(self.tentative_keys@[i as int] == key);
                            break;
                        }
                        i += 1;
                    }
                    proof {
                        if i >= self.tentative_keys@.len() {
                            assert(false);
                        }
                        assert(i < self.tentative_keys@.len());
                    }
                    self.tentative.remove(key);
                    self.tentative_keys.remove(i);

                    proof {
                        assert(!self.tentative_keys@.contains(*key));

                        assert forall |k| old(self).tentative_keys@.contains(k) && k != key implies 
                            self.tentative_keys@.contains(k)
                        by {
                            let witness = choose |i: int| 0 <= i < old(self).tentative_keys@.len() && old(self).tentative_keys@[i] == k;
                            assert(witness != i);
                            if witness < i {
                                assert(self.tentative_keys@[witness] == old(self).tentative_keys@[witness]);
                            } else {
                                assert(witness > i);
                                assert(self.tentative_keys@[witness - 1] == old(self).tentative_keys@[witness]);
                            }
                        }

                        assert(self.tentative@.dom() == old(self).tentative@.dom().remove(*key));
                        assert(self.tentative@.dom() =~= self.tentative_keys@.to_set());
                        assert(self.tentative_view().contents == old(self).tentative_view().remove(*key).contents);
                        assert(self.valid());
                    }

                    Ok(header_addr)
                }
                PendingIndexEntry::ReplaceExisting(entry) => {
                    // the key already exists; we need to delete it as normal.
                    let header_addr = self.delete_existing_key(key);
                    Ok(header_addr)
                }
                // If the key has a tentative entry but it's not created,
                // it can't be deleted.
                _ => return Err(KvError::KeyNotFound)
            }
        } else if self.m.contains_key(key) {
            let header_addr = self.delete_existing_key(key);
            Ok(header_addr)
        } else {
            Err(KvError::KeyNotFound)
        }
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
}

impl<K> VolatileKvIndexImpl<K>
where
    K: PmCopy + Hash + Eq + KeyEq + Clone + Sized + std::fmt::Debug,
{
    proof fn lemma_valid_implies_view_valid(&self)
        requires
            self.valid(),
        ensures
            self@.valid(),
    {
        assert forall |k| #[trigger] self@.contains_key(k) implies self@.contents[k].valid() by {
            self.m@[k].lemma_num_locations_is_entry_locations_len();
        }
    }

    pub proof fn lemma_if_no_tentative_entries_then_tentative_view_matches_view(self)
        requires 
            self.valid(),
            self.tentative@.is_empty()
        ensures 
            self@ == self.tentative_view()
    {
        // extensional equality
        assert(self@.contents =~= self.tentative_view().contents);
    }

    pub exec fn abort_transaction(&mut self)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            self@ == self.tentative_view(),
            self@ == old(self)@,
            self.num_tentative_entries() == 0,
    {
        self.tentative.clear();
        self.tentative_keys.clear();
        proof {
            assert(self.tentative@ =~= Map::<K, PendingIndexEntry>::empty());
            assert(self.tentative_keys@ == Seq::<K>::empty());
            assert(self.tentative@.dom() == self.tentative_keys@.to_set());

            self.lemma_if_no_tentative_entries_then_tentative_view_matches_view();
        }
    }

    pub exec fn commit_transaction(&mut self)
        requires 
            old(self).valid()
        ensures 
            self.valid(),
            self@ == self.tentative_view(),
            self@ == old(self).tentative_view(),
            self.num_tentative_entries() == 0,
    {
        if self.tentative_keys.len() == 0 {
            proof {
                self.lemma_if_no_tentative_entries_then_tentative_view_matches_view();
            }
            return;
        }

        while self.tentative_keys.len() > 0 
            invariant 
                0 < self.num_list_entries_per_node,
                self.tentative@.dom().finite(),
                forall |k| #[trigger] self.m@.contains_key(k) ==> self.m@[k].valid(),
                forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
                    &&& self.tentative@[k] is Created ==> {
                            &&& self.tentative@[k] matches PendingIndexEntry::Created(entry)
                            &&& entry.valid()
                            &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
                        }
                    &&& self.tentative@[k] is ReplaceExisting ==> {
                            &&& self.tentative@[k] matches PendingIndexEntry::ReplaceExisting(entry)
                            &&& entry.valid()
                            &&& entry.num_list_entries_per_node == self.num_list_entries_per_node
                        }
                    },
                forall |k| #[trigger] self.m@.contains_key(k) ==>
                    self.m@[k].num_list_entries_per_node@ == self.num_list_entries_per_node,
                vstd::std_specs::hash::obeys_key_model::<K>(),
                self.tentative@.dom() == self.tentative_keys@.to_set(),
                self.tentative_keys@.no_duplicates(),
                forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
                    ||| self.tentative@[k] is Created 
                    ||| self.tentative@[k] is Deleted
                    ||| self.tentative@[k] is ReplaceExisting
                },
                self@.num_list_entries_per_node == old(self).tentative_view().num_list_entries_per_node,
                // the tentative view remains the same as we update the true index
                self.tentative_view() == old(self).tentative_view(),

                self.valid(),
        {
            let ghost pre_key_list = self.tentative_keys@;
            let ghost pre_key_map = self.tentative@;
            let ghost pre_tentative_view = self.tentative_view();
            let ghost pre_self = *self;
            broadcast use vstd::std_specs::hash::group_hash_axioms;

            let current_tentative_key = self.tentative_keys.pop();
            let key = current_tentative_key.unwrap();
            
            let key_clone = key.clone_provable();
            
            match self.tentative.remove(&key).unwrap() {
                PendingIndexEntry::Created(entry) | PendingIndexEntry::ReplaceExisting(entry) => {
                    self.m.insert(key_clone, entry);
                }
                PendingIndexEntry::Deleted => {
                    self.m.remove(&key);
                    assert(!self.m@.contains_key(key));
                }
            }

            assert(forall |i: int| 0 <= i < self.tentative_keys@.len() ==> 
                self.tentative_keys@[i] == #[trigger] pre_key_list[i]);
            assert(self.tentative_keys@.to_set() == pre_key_list.to_set().remove(key));
            assert(self.tentative@ == pre_key_map.remove(key));

            assert(self.tentative_view().contents =~= pre_tentative_view.contents);
            assert(self.tentative_view() == old(self).tentative_view());
        }

        proof {
            self.lemma_if_no_tentative_entries_then_tentative_view_matches_view();
        }
    }

    exec fn delete_existing_key(&mut self, key: &K) -> (out: u64)
        requires 
            old(self).valid(),
            old(self).m@.contains_key(*key),
            !old(self).tentative@.contains_key(*key) || old(self).tentative@[*key] is ReplaceExisting,
            old(self).tentative_view().contents.contains_key(*key),
        ensures
            self.valid(),
            out == old(self).tentative_view().contents[*key].header_addr,
            self.tentative_view() == old(self).tentative_view().remove(*key),
            old(self).m@ == self.m@,

    {
        broadcast use vstd::std_specs::hash::group_hash_axioms;

        let header_addr = if let Some(entry) = self.tentative.get(key) {
            match entry {
                PendingIndexEntry::ReplaceExisting(entry) => entry.header_addr,
                _ => {
                    // we have to return something here to satisfy the compiler, 
                    // but the precondition ensures this will never happen, so it 
                    // doesn't matter what it is
                    assert(false);
                    0
                },
            }
        } else {
            self.m.get(key).unwrap().header_addr
        };
        let new_pending_entry = PendingIndexEntry::Deleted;
        let key_clone = key.clone_provable();
        let key_clone2 = key.clone_provable();
        if self.tentative.get(key).is_none() {
            self.tentative_keys.push(key_clone2);
            assert(self.tentative_keys@.subrange(0, self.tentative_keys@.len() - 1) == old(self).tentative_keys@);
            assert(self.tentative_keys@[self.tentative_keys@.len() - 1] == key);
        }
        self.tentative.insert(key_clone, new_pending_entry);

        assert(self.tentative@.dom() == old(self).tentative@.dom().insert(*key));
        assert(self.tentative@.dom() =~= self.tentative_keys@.to_set());
        assert(self.tentative_view().contents == old(self).tentative_view().remove(*key).contents);
        assert(self.valid());

        header_addr
    }
}

}
