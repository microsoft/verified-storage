//! A `DurableKvStore` represents the durable components of a `PagedKv`. It is generic
//! to allow for different PM abstractions, persistent layouts, etc.
//! It should refine an array where each element optionally contains a key, a header,
//! and a list of pages. This structure encompasses all of the durable KV entries,
//! so we aren't distinguishing between separate physical memory regions. I think
//! we want to stay at a higher level of abstraction here to make it easier to jump
//! up to the overall KV store

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::interface_t::*;
use crate::paged_kv::volatile::volatileimpl_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
    pub struct DurableKvStoreViewEntry<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        key: K,
        header: H,
        pages: Seq<P>,
    }

    pub struct DurableKvStoreView<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        contents: Seq<Option<DurableKvStoreViewEntry<K, H, P>>>
    }

    impl<K, H, P> DurableKvStoreView<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub closed spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            forall |k: K| volatile_index.contains_key(k) <==>
            {
                let entry = self.contents[volatile_index.index(k) as int];
                match entry {
                    Some(entry) => entry.key == k,
                    None => false
                }
            }

        }
    }

    pub trait DurableKvStore<PM, K, H, P, E> : Sized
    where
        PM: PersistentMemoryRegions,
        K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
        H: Serializable<E> + std::fmt::Debug,
        P: Serializable<E> + LogicalRange + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> DurableKvStoreView<K, H, P>;

        fn new(pmem: PM,
            kvstore_id: u128,
            max_keys: usize,
            lower_bound_on_max_pages: usize,
            logical_range_gaps_policy: LogicalRangeGapsPolicy
        ) -> Result<Self, PagedKvError<K, E>>;
    }
}
