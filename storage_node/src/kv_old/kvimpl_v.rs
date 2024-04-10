//! This file contains the verified implementation of the KV store. The methods
//! defined here are meant to be called by methods in kvimpl_t.rs with `Perm`
//! arguments that have been audited along with the rest of that file.
//!
//! The UntrustedKvStoreImpl is split into two key components: a volatile index
//! and a durable store. Each of these may be further split into separate components,
//! but having a high-level split between volatile and durable should make the
//! distinction between updates that require crash-consistency proofs, and updates
//! that don't, clear. The view of an UntrustedKvStoreImpl is obtained using the contents
//! of its current volatile and durable components.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use super::durable::durableimpl_v::*;
use super::durable::durablespec_t::*;
use super::inv_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;

use std::hash::Hash;

verus! {

pub struct UntrustedKvStoreImpl<PM, K, H, P, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
    H: Serializable<E> + Header<K> + std::fmt::Debug,
    P: Serializable<E> + LogicalRange + std::fmt::Debug,
    D: DurableKvStore<PM, K, H, P, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    id: u128,
    durable_store: D,
    volatile_index: V,
    _phantom: Ghost<core::marker::PhantomData<(PM, K, H, P, E)>>,
}

impl<PM, K, H, P, D, V, E> UntrustedKvStoreImpl<PM, K, H, P, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + Serializable<E> + Sized + std::fmt::Debug,
    H: Serializable<E> + Header<K> + Sized + std::fmt::Debug,
    P: Serializable<E> + LogicalRange + std::fmt::Debug,
    D: DurableKvStore<PM, K, H, P, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{

    // This function specifies how all durable contents of the KV
    // should be viewed upon recovery as an abstract paged KV state.
    // TODO: write this
    pub closed spec fn recover(mems: Seq<Seq<u8>>, kv_id: u128) -> Option<AbstractKvStoreState<K, H, P>>
    {
        None
    }

    pub closed spec fn view(&self) -> AbstractKvStoreState<K, H, P>
    {
        AbstractKvStoreState {
            id: self.id,
            contents: Map::new(
                |k| { self.volatile_index@.contains_key(k) },
                |k| {
                    let index_entry = self.volatile_index@[k];
                    match index_entry {
                        Some(index_entry) => {
                            match self.durable_store@[index_entry.metadata_offset] {
                                Some(entry) => (
                                    // pages seq only includes the entries themselves, not their physical offsets
                                    entry.header(), entry.page_entries()
                                ),
                                None => {
                                    // This case is unreachable, because we only include indexes that exist,
                                    // but we have to return something, so pick a random entry and return its header.
                                    // NOTE: could return H::default() if we add Default as a trait bound on H.
                                    let arbitrary_entry = choose |e: DurableKvStoreViewEntry<K, H, P>| e.key() == k;
                                    ( arbitrary_entry.header(), Seq::empty() )
                                }
                            }
                        }
                        None => {
                            // This case is unreachable, because we only include indexes that exist,
                            // but we have to return something, so pick a random entry and return its header.
                            // NOTE: could return H::default() if we add Default as a trait bound on H.
                            let arbitrary_entry = choose |e: DurableKvStoreViewEntry<K, H, P>| e.key() == k;
                            ( arbitrary_entry.header(), Seq::empty() )}
                    }
                }
            )
        }
    }

    closed spec fn durable_store_contents_match_kv_state(self, durable_store_state: DurableKvStoreView<K, H, P>) -> bool
    {
        let kv_state = self@;
        ||| kv_state.empty() && durable_store_state.empty()
        ||| ({
            // everything in the durable store is in the kv view
            &&& forall |i: int| 0 <= i < durable_store_state.len() ==> {
                    match #[trigger] durable_store_state[i] {
                        Some(durable_entry) => {
                            let key = durable_entry.key();
                            match kv_state[key] {
                                Some(kv_entry) => {
                                    &&& kv_entry.0 == durable_entry.header()
                                    &&& kv_entry.1 == durable_entry.page_entries()
                                }
                                None => false
                            }
                        }
                        None => true
                    }
                }
            // all keys in the kv view are also in the durable store
            &&& forall |k: K| kv_state.contents.contains_key(k) ==> {
                    match self.volatile_index@[k] {
                        Some(index_entry) => {
                            let durable_entry = durable_store_state[index_entry.metadata_offset as int];
                            let kv_entry = kv_state[k];
                            // we already checked that the entries match, so we just need to make sure
                            // that there are no keys that exist in the kv view that do not exist
                            // in the durable store here
                            match (kv_entry, durable_entry) {
                                (Some(_), Some(_)) => true,
                                (_, _) => false
                            }
                        }
                        None => false
                    }
                }
        })
    }

    // Proves that if the durable store and volatile index comprising a KV are both empty,
    // then the view of the KV is also empty.
    proof fn lemma_empty_kv(self)
        requires
            self.durable_store@.empty(),
            self.volatile_index@.empty(),
        ensures
            self@.empty()
    {
        lemma_empty_map_contains_no_keys(self.volatile_index@.contents);
        assert(Set::new(|k| self.volatile_index@.contains_key(k)) =~= Set::<K>::empty());
        assume(false);
    }

    // Proves that creating a new key/header pair in the durable and volatile
    // components results in the creation of the same key/header entry in
    // the abstract KV store.
    proof fn lemma_create_in_durable_and_volatile_implies_create_in_kv_view(
        old_kv: UntrustedKvStoreImpl<PM, K, H, P, D, V, E>,
        new_kv: UntrustedKvStoreImpl<PM, K, H, P, D, V, E>,
        k: K,
        h: H,
        offset: int,
    )
        requires
            old_kv.valid(),
            k == h.spec_key(),
            0 <= offset < old_kv.durable_store@.len(),
            new_kv.durable_store@ == old_kv.durable_store@.create(offset, h),
            new_kv.durable_store@[offset].is_Some(),
            new_kv.volatile_index@ == old_kv.volatile_index@.insert_metadata_offset(k, offset),
        ensures
            new_kv@ == old_kv@.create(k, h),
            new_kv.durable_store_contents_match_kv_state(new_kv.durable_store@),
            new_kv.durable_store@.matches_volatile_index(new_kv.volatile_index@)
    {

        // // the new kv has the same keys as the old kv plus the created key
        // assert(old_kv@.get_keys() == old_kv.volatile_index@.keys());
        // assert(new_kv.volatile_index@.keys() =~= old_kv.volatile_index@.keys().insert(k));
        // assert(new_kv@.get_keys() == old_kv@.get_keys().insert(k));

        // TODO: finish
        assume(false);

        // // the new key in the new kv has the right header and page values
        // // TODO: unclear if proving this will actually help us prove the postconditions?
        // match new_kv.durable_store@[offset] {
        //     Some(durable_entry) => {
        //         assert(durable_entry.key() == k);
        //         assert(durable_entry.header() == h);
        //         assert(durable_entry.page_entries() == Seq::<P>::empty());

        //         // the new key in the new kv has the right associated value
        //         match new_kv@[k] {
        //             Some((header, pages)) => {
        //                 assert(header == durable_entry.header());
        //                 assert(header.spec_key() == durable_entry.key());
        //                 assert(durable_entry.page_entries() == pages);

        //                 assert(header == h);
        //                 assert(header.spec_key() == k);
        //                 assert(pages == Seq::<P>::empty());
        //             }
        //             None => assert(false)
        //         }
        //     }
        //     None => assert(false)
        // }
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store_contents_match_kv_state(self.durable_store@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()
    }

    pub fn untrusted_new(
        pmem: PM,
        kvstore_id: u128,
        max_keys: usize,
        lower_bound_on_max_pages: usize,
        logical_range_gaps_policy: LogicalRangeGapsPolicy,
    ) -> (result: Result<Self, KvError<K, E>>)
        ensures
            match result {
                Ok(new_kv) => {
                    &&& new_kv.valid()
                }
                Err(_) => true
            }
    {
        let durable_store = D::new(pmem, kvstore_id, max_keys, lower_bound_on_max_pages, logical_range_gaps_policy)?;
        let volatile_index = V::new(kvstore_id, max_keys)?;
        let kv = Self {
            id: kvstore_id,
            durable_store,
            volatile_index,
            _phantom: Ghost(spec_phantom_data()),
        };
        proof {
            lemma_empty_index_matches_empty_store(durable_store@, volatile_index@);
            kv.lemma_empty_kv();
        }
        Ok(kv)
    }

    pub fn untrusted_create(
        &mut self,
        key: &K,
        header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid(),
            key == header.spec_key(),
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.create(*key, header)
                }
                Err(_) => true // TODO
            }
    {
        let ghost old_kv = *self;

        // `header` stores its own key, so we don't have to pass its key to the durable
        // store separately.
        let offset = self.durable_store.create(header, perm)?;
        self.volatile_index.insert(key, offset)?;
        proof {
            Self::lemma_create_in_durable_and_volatile_implies_create_in_kv_view(old_kv, *self, *key, header, offset as int);
            assert(self.durable_store_contents_match_kv_state(self.durable_store@));
            assert(self.durable_store@.matches_volatile_index(self.volatile_index@));
        }
        Ok(())
    }

    pub fn untrusted_read_header(&self, key: &K) -> (result: Option<&H>)
        requires
            self.valid()
        ensures
        ({
            let spec_result = self@.read_header_and_pages(*key);
            match (result, spec_result) {
                (Some(output_header), Some((spec_header, pages))) => {
                    &&& spec_header == output_header
                }
                _ => {
                    let spec_result = self@.read_header_and_pages(*key);
                    spec_result.is_None()
                }
            }
        })
    {
        assume(false); // TODO

        // First, get the offset of the header in the durable store using the volatile index
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_header(offset),
            None => None
        }
    }

    // TODO: return a Vec<&P> to save space/reduce copies
    pub fn untrusted_read_header_and_pages(&self, key: &K) -> (result: Option<(&H, &Vec<P>)>)
        requires
            self.valid(),
        ensures
        ({
            let spec_result = self@.read_header_and_pages(*key);
            match (result, spec_result) {
                (Some((output_header, output_pages)), Some((spec_header, spec_pages))) => {
                    &&& spec_header == output_header
                    &&& spec_pages == output_pages@
                }
                _ => {
                    let spec_result = self@.read_header_and_pages(*key);
                    spec_result.is_None()
                }
            }
        })
    {
        assume(false);
        // First, get the offset of the header in the durable store using the volatile index
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_header_and_pages(offset),
            None => None
        }
    }

    pub fn untrusted_read_pages(&self, key: &K) -> (result: Option<&Vec<P>>)
        requires
            self.valid(),
        ensures
        ({
            let spec_result = self@.read_header_and_pages(*key);
            match (result, spec_result) {
                (Some( output_pages), Some((spec_header, spec_pages))) => {
                    &&& spec_pages == output_pages@
                }
                _ => {
                    let spec_result = self@.read_header_and_pages(*key);
                    spec_result.is_None()
                }
            }
        })
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_pages(offset),
            None => None
        }
    }

    pub fn untrusted_update_header(
        &mut self,
        key: &K,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    self@ == old(self)@.update_header(*key, new_header)
                }
                Err(KvError::KeyNotFound) => {
                    self@[*key].is_None()
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.update_header(offset, new_header),
            None => Err(KvError::KeyNotFound)
        }
    }

    pub fn untrusted_delete(
        &mut self,
        key: &K,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.delete(*key)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        // Remove the entry from the volatile index, obtaining the physical offset as the return value
        let offset = self.volatile_index.remove(key)?;
        self.durable_store.delete(offset, perm)
    }

    pub fn untrusted_find_page_with_logical_range_start(&self, key: &K, start: usize) -> (result: Result<Option<usize>, KvError<K, E>>)
        requires
            self.valid()
        ensures
            match result {
                Ok(page_idx) => {
                    let spec_page = self@.find_page_with_logical_range_start(*key, start as int);
                    // page_idx is an Option<usize> and spec_page is an Option<int>, so we can't directly
                    // compare them and need to use a match statement here.
                    match (page_idx, spec_page) {
                        (Some(page_idx), Some(spec_idx)) => {
                            &&& page_idx == spec_idx
                        }
                        (None, None) => true,
                        _ => true // TODO
                    }
                }
                Err(_) => true // TODO
            }
    {
        // TODO: discuss how this will be implemented.
        // 1. will we search in PM or in memory?
        // 2. will the PM-resident entries be sorted?
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_find_pages_in_logical_range(
        &self,
        key: &K,
        start: usize,
        end: usize
    ) -> (result: Result<Vec<&P>, KvError<K, E>>)
        requires
            self.valid()
        ensures
            true
            // TODO: this match statement breaks something in Verus
            // match result {
            //     Ok(output_pages) =>  {
            //         let spec_pages = self@.find_pages_in_logical_range(*key, start as int, end as int);
            //         let spec_pages_ref = Seq::new(spec_pages.len(), |i| { &spec_pages[i] });
            //         output_pages@ == spec_pages_ref
            //     }
            //     Err(_) => true // TODO
            // }
    {
        // TODO: like find_page_with_logical_range_start, implementation depends on what
        // we want to do in volatile vs. durable components
        Err(KvError::NotImplemented)
    }

    pub fn untrusted_append_page(
        &mut self,
        key: &K,
        new_index: P,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.append_page(*key, new_index)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        // append a page to the list rooted at this offset
        let page_offset = match offset {
            Some(offset) => self.durable_store.append(offset, new_index, perm)?,
            None => return Err(KvError::KeyNotFound)
        };
        // add the durable location of the page to the in-memory list
        self.volatile_index.append_offset_to_list(key, page_offset)
    }

    pub fn untrusted_append_page_and_update_header(
        &mut self,
        key: &K,
        new_index: P,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.append_page_and_update_header(*key, new_index, new_header)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let offset = self.volatile_index.get(key);
        // update the header at this offset append a page to the list rooted there
        let page_offset = match offset {
            Some(offset) => self.durable_store.update_header_and_append(offset, new_index, new_header, perm)?,
            None => return Err(KvError::KeyNotFound)
        };
         // add the durable location of the page to the in-memory list
         self.volatile_index.append_offset_to_list(key, page_offset)
    }

    pub fn untrusted_update_page(
        &mut self,
        key: &K,
        idx: usize,
        new_index: P,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.update_page(*key, idx, new_index)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let entry_offset = self.volatile_index.get_entry_location_by_index(key, idx);
        match (header_offset, entry_offset) {
            (Some(header_offset), Ok(entry_offset)) => self.durable_store.update_page(header_offset, entry_offset, new_index, perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_update_page_and_header(
        &mut self,
        key: &K,
        idx: usize,
        new_index: P,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.update_page_and_header(*key, idx, new_index, new_header)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let entry_offset = self.volatile_index.get_entry_location_by_index(key, idx);
        match (header_offset, entry_offset) {
            (Some(header_offset), Ok(entry_offset)) => self.durable_store.update_page_and_header(header_offset, entry_offset, new_header, new_index,  perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_trim_pages(
        &mut self,
        key: &K,
        trim_length: usize,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.trim_pages(*key, trim_length as int)
                }
                Err(_) => true // TODO
            }
    {
        // use the volatile index to figure out which physical offsets should be removed
        // from the list, then use that information to trim the list on the durable side
        // TODO: trim_length is in terms of list entries, not bytes, right? Check Jay's impl
        // note: we trim from the beginning of the list, not the end
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let new_list_head_offset = self.volatile_index.trim_list(key, trim_length);
        match (header_offset, new_list_head_offset) {
            (Some(header_offset), Ok(new_list_head_offset)) => self.durable_store.trim_list(header_offset, new_list_head_offset, trim_length, perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_trim_pages_and_update_header(
        &mut self,
        key: &K,
        trim_length: usize,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), KvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.trim_pages_and_update_header(*key, trim_length as int, new_header)
                }
                Err(_) => true // TODO
            }
    {
        assume(false);
        let header_offset = self.volatile_index.get(key);
        let new_list_head_offset = self.volatile_index.trim_list(key, trim_length);
        match (header_offset, new_list_head_offset) {
            (Some(header_offset), Ok(new_list_head_offset)) => self.durable_store.trim_list_and_update_header(header_offset, new_list_head_offset, trim_length, new_header, perm),
            (None, _) => Err(KvError::KeyNotFound),
            (_, Err(KvError::IndexOutOfRange)) => Err(KvError::IndexOutOfRange),
            (_, Err(_)) => Err(KvError::InternalError), // TODO: better error handling for all cases
        }
    }

    pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
        requires
            self.valid()
        ensures
            result@.to_set() == self@.get_keys()
    {
        assume(false);
        self.volatile_index.get_keys()
    }

}

}
