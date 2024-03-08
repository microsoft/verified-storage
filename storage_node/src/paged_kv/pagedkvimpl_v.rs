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
    H: Serializable<E> + std::fmt::Debug,
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
    K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
    H: Serializable<E> + std::fmt::Debug,
    P: Serializable<E> + LogicalRange + std::fmt::Debug,
    D: DurableKvStore<PM, K, H, P, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{

    pub closed spec fn view(&self) -> AbstractKvStoreState<K, H, P>
    {
        AbstractKvStoreState {
            id: self.id,
            contents: Map::new(
                |k| { self.volatile_index@.contains_key(k) },
                |k| {
                    let idx = self.volatile_index@.index(k) as int;
                    match self.durable_store@[idx] {
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
            )
        }
    }

    pub closed spec fn valid(self) -> bool
    {
        self.durable_store@.matches_volatile_index(self.volatile_index@)
    }

    pub fn new(
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
        assume(false); // TODO: prove
        Ok(
            Self {
                id: kvstore_id,
                durable_store: D::new(pmem, kvstore_id, max_keys, lower_bound_on_max_pages, logical_range_gaps_policy)?,
                volatile_index: V::new(kvstore_id, max_keys)?,
                _phantom: Ghost(spec_phantom_data()),
            }
        )
    }
}

}
