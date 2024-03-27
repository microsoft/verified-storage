#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::durable::durableimpl_v::*;
use super::durable::durablespec_t::*;
use super::pagedkvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::paged_kv::pagedkvimpl_t::*;
use crate::pmem::pmemspec_t::*;

use std::hash::Hash;

verus! {

pub struct UntrustedPagedKvImpl<PM, K, H, P, D, V, E>
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

impl<PM, K, H, P, D, V, E> UntrustedPagedKvImpl<PM, K, H, P, D, V, E>
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
                    let idx = self.volatile_index@[k];
                    match idx {
                        Some(idx) => {
                            match self.durable_store@[idx as int] {
                                Some(entry) => (
                                    entry.header(), entry.pages()
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

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()
    }

    pub fn untrusted_new(
        pmem: PM,
        kvstore_id: u128,
        max_keys: usize,
        lower_bound_on_max_pages: usize,
        logical_range_gaps_policy: LogicalRangeGapsPolicy,
    ) -> (result: Result<Self, PagedKvError<K, E>>)
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
        proof { lemma_empty_index_matches_empty_store(durable_store@, volatile_index@); }
        Ok(
            Self {
                id: kvstore_id,
                durable_store,
                volatile_index,
                _phantom: Ghost(spec_phantom_data()),
            }
        )
    }

    pub fn untrusted_create(
        &mut self,
        key: &K,
        header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
        requires
            old(self).valid(),
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.create(*key, header)
                }
                Err(_) => true // TODO
            }
    {
        // `header` stores its own key, so we don't have to pass its key to the durable
        // store separately.
        let offset = self.durable_store.create(header, perm)?;
        self.volatile_index.insert(key, offset)?;
        assume(false); // TODO
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
        None
    }

    pub fn untrusted_update_header(
        &mut self,
        key: &K,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
        requires
            old(self).valid(),
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.update_header(*key, new_header)
                }
                Err(_) => true // TODO
            }
    {
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_delete(
        &mut self,
        key: &K,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_find_page_with_logical_range_start(&self, key: &K, start: usize) -> (result: Result<Option<usize>, PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_find_pages_in_logical_range(
        &self,
        key: &K,
        start: usize,
        end: usize
    ) -> (result: Result<Vec<&P>, PagedKvError<K, E>>)
        requires
            self.valid()
        ensures
            match result {
                Ok(output_pages) =>  {
                    let spec_pages = self@.find_pages_in_logical_range(*key, start as int, end as int);
                    let spec_pages_ref = Seq::new(spec_pages.len(), |i| { &spec_pages[i] });
                    output_pages@ == spec_pages_ref
                }
                Err(_) => true // TODO
            }
    {
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_append_page(
        &mut self,
        key: &K,
        new_index: P,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_append_page_and_update_header(
        &mut self,
        key: &K,
        new_index: P,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_update_page(
        &mut self,
        key: &K,
        idx: usize,
        new_index: P,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_update_page_and_header(
        &mut self,
        key: &K,
        idx: usize,
        new_index: P,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_trim_pages(
        &mut self,
        key: &K,
        trim_length: usize,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_trim_pages_and_update_header(
        &mut self,
        key: &K,
        trim_length: usize,
        new_header: H,
        perm: Tracked<&TrustedKvPermission<PM, K, H, P, D, E>>
    ) -> (result: Result<(), PagedKvError<K, E>>)
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
        Err(PagedKvError::NotImplemented)
    }

    pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
        requires
            self.valid()
        ensures
            result@.to_set() == self@.get_keys()
    {
        assume(false);
        Vec::new()
    }

}

}
