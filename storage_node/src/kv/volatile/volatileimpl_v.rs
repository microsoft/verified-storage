//! This file contains a trait that defines the interface for the high-level
//! volatile component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::clone::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use crate::kv::durable::commonlayout_v::EntryStatus;
use crate::kv::volatile::volatilespec_v::*;
use crate::pmem::pmcopy_t::*;
use std::collections::HashMap;
use std::hash::Hash;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

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

pub struct PendingIndexEntry {
    pub status: EntryStatus,
    pub entry: VolatileKvIndexEntryImpl
}

impl PendingIndexEntry {
    pub open spec fn view(self) -> VolatileKvIndexEntry 
    {
        self.entry@
    }
}

#[verifier::reject_recursive_types(K)]
pub struct VolatileKvIndexImpl<K>
where
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
{
    pub m: HashMap<K, VolatileKvIndexEntryImpl>,
    pub tentative: HashMap<K, PendingIndexEntry>, // TODO prob need to differentiate deleted vs created?
    pub tentative_keys: Vec<K>,
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

    open spec fn num_tentative_entries(self) -> nat {
        self.tentative_keys@.len()
    }

    open spec fn tentative_view(&self) -> VolatileKvIndexView<K>
    {
        let outstanding_keys_to_add = self.tentative@.dom().filter(
            |k| self.tentative@[k].status is Created
        );
        let outstanding_keys_to_delete = self.tentative@.dom().filter(
            |k| self.tentative@[k].status is Deleted
        );
        // we don't do anything with keys that were created AND deleted in this 
        // transaction 
        let keys = self.m@.dom().union(outstanding_keys_to_add) - outstanding_keys_to_delete;
        VolatileKvIndexView::<K> {
            contents: Map::new(
                |k| keys.contains(k),
                |k| if self.tentative@.contains_key(k) {
                        self.tentative@[k]@
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
            ||| self.tentative@[k].status is Created 
            ||| self.tentative@[k].status is Deleted
        }
        // if a key was deleted (but not created) in the current transaction,
        // it must already exist
        &&& forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k].status is Deleted ==>
                self.m@.contains_key(k)
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
        let key_clone = key.clone();
        assume(*key == key_clone); // TODO: How do we get Verus to believe this?
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
        let key_clone = key.clone();
        let key_clone2 = key.clone();
        assume(*key == key_clone); // TODO: How do we get Verus to believe this?
        assume(*key == key_clone2); // and this?

        let new_entry = PendingIndexEntry {
            status: EntryStatus::Created,
            entry,
        };
        
        if !self.tentative.contains_key(key) {
            assert(!self.tentative_keys@.contains(*key));
            // if tentative doesn't already contain the key,
            // it must have been deleted and re-created in this transaction.
            // we only add it to tentative_keys if it's not already in there
            self.tentative_keys.push(key_clone2);
            assert(self.tentative_keys@ == old(self).tentative_keys@.push(*key));
            assert(self.tentative_keys@[self.tentative_keys@.len() - 1] == *key);
            assert(self.tentative_keys@.subrange(0, old(self).tentative_keys@.len() as int) == old(self).tentative_keys@);
        } else {
            assert(self.tentative_keys@.contains(*key));
        }
        self.tentative.insert(key_clone, new_entry);
        
        assert(self.tentative_view().contents == old(self).tentative_view().insert_key(*key, header_addr).contents);
        assert(self.tentative@.dom() == self.tentative_keys@.to_set());

        assert(self.tentative_keys@.no_duplicates());

        assert(forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
            ||| self.tentative@[k].status is Created 
            ||| self.tentative@[k].status is Deleted
        });

        assert(forall |k| #[trigger] self.tentative@.contains_key(k) && self.tentative@[k].status is Deleted ==>
            self.m@.contains_key(k));

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
                match entry.status {
                    EntryStatus::Created => Some(entry.entry.header_addr),
                    EntryStatus::Deleted => None,
                    _ => {
                        assert(false);
                        None
                    }
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
        assume(false);

        assert(self@.valid()) by {
            self.lemma_valid_implies_view_valid();
        }

        // TODO @hayley THURSDAY
        // If the entry already exists:
        //   - if it's only in the committed index, create a pending delete 
        //   - if it's in tentative with status Created, remove it 
        //     from the tentative map & list
        //   - if it's in tentative with status Deleted, return error
        //   - if none of these are true, return error 

        // let old_entry = if self.tentative.contains_key(key) {
        //     self.tentative.get(key).unwrap()
        // } else if self.m.contains_key(key) {
        //     self.m.get(key).unwrap()
        // } else {
        //     return Err(KvError::KeyNotFound);
        // }

        // let delete_entry = PendingIndexEntry {
        //     status: EntryStatus::Deleted
        // }

        // if !self.tentative.contains_key(key) {
        //     assert(!self.tentative_keys@.contains(*key));
        //     // if tentative doesn't already contain the key,
        //     // it must have been deleted and re-created in this transaction.
        //     // we only add it to tentative_keys if it's not already in there
        //     self.tentative_keys.push(key_clone2);
        //     assert(self.tentative_keys@ == old(self).tentative_keys@.push(*key));
        //     assert(self.tentative_keys@[self.tentative_keys@.len() - 1] == *key);
        //     assert(self.tentative_keys@.subrange(0, old(self).tentative_keys@.len() as int) == old(self).tentative_keys@);
        // } else {
        //     assert(self.tentative_keys@.contains(*key));
        // }

        // result
        Err(KvError::NotImplemented)
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
    K: Hash + Eq + Clone + Sized + std::fmt::Debug,
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

    // pub proof fn lemma_if_tentative_view_matches_view_then_no_tentative_entries(self)
    //     requires 
    //         self.valid(),
    //         self@ == self.tentative_view(),
    //     ensures 
    //         self.tentative@.is_empty()
    // {
    //     let outstanding_keys_to_add = self.tentative@.dom().filter(
    //         |k| self.tentative@[k].status is Created
    //     );
    //     let outstanding_keys_to_delete = self.tentative@.dom().filter(
    //         |k| self.tentative@[k].status is Deleted
    //     );
    //     assert(outstanding_keys_to_add.disjoint(outstanding_keys_to_delete));
    //     // assert(outstanding_keys_to_add.union(outstanding_keys_to_delete) == self.tentative@.dom());
    //     // vstd::set_lib::lemma_set_disjoint(outstanding_keys_to_add, outstanding_keys_to_delete);
    //     // vstd::set_lib::lemma_set_properties::<K>();

    //     let keys = (self.m@.dom().union(outstanding_keys_to_add)) - outstanding_keys_to_delete;
    //     assert(self.tentative_view().contents.dom() == keys);
    //     assert(self@.contents.dom() == keys);
    //     assert(self.m@.dom() =~= keys);

    //     assert(forall |k| #[trigger] keys.contains(k) ==> self.m@.dom().contains(k));
    //     assert(forall |k| keys.contains(k) ==> !outstanding_keys_to_add.contains(k));
    //     assert(forall |k| keys.contains(k) ==> !outstanding_keys_to_delete.contains(k));

    //     assert(outstanding_keys_to_add == Set::<K>::empty());

    //     assert(outstanding_keys_to_delete == Set::<K>::empty()) by {
    //         // proof by contradiction. suppose there is a key in the set
    //         if exists |k| outstanding_keys_to_delete.contains(k) {
    //             let k = choose |k| outstanding_keys_to_delete.contains(k);
    //             assert(!keys.contains(k));
    //             assert(false);
    //         } else {
    //             assert(outstanding_keys_to_delete == Set::<K>::empty());
    //         }
    //     }

    //     assert(self.tentative@.dom() =~= Set::empty());

    //     assert(forall |k| self@.contents.contains_key(k) ==> 
    //         !(#[trigger] self.tentative@.contains_key(k)));        
    // }

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
        assume(false); // TODO @hayley
        // iterate over modified indices, adding newly-created ones
        // to the main index and deleting removed ones
        let mut index = 0;
        while index < self.tentative_keys.len() 
            invariant
                0 < self.num_list_entries_per_node,
                self.tentative@.dom().finite(),
                forall |k| #[trigger] self.m@.contains_key(k) ==> self.m@[k].valid(),
                forall |k| #[trigger] self.m@.contains_key(k) ==>
                    self.m@[k].num_list_entries_per_node@ == self.num_list_entries_per_node,
                vstd::std_specs::hash::obeys_key_model::<K>(),
                // forall |k| #[trigger] self@.contents.contains_key(k) && self.tentative@.contains_key(k) ==>
                //     self@.contents[k] != self.tentative@[k]@,
                self.tentative@.dom() == self.tentative_keys@.to_set(),
                self.tentative_keys@.no_duplicates(),
                forall |k| #[trigger] self.tentative@.contains_key(k) ==> {
                    ||| self.tentative@[k].status is Created 
                    ||| self.tentative@[k].status is Updated
                },
        {
            index += 1;
        }

        self.tentative.clear();
        self.tentative_keys.clear();
        proof {
            assert(self.tentative@ =~= Map::<K, PendingIndexEntry>::empty());
            assert(self.tentative_keys@ == Seq::<K>::empty());
            assert(self.tentative@.dom() == self.tentative_keys@.to_set());

            self.lemma_if_no_tentative_entries_then_tentative_view_matches_view();
        }
    }
}

}
