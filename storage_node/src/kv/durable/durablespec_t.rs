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

use crate::kv::kvimpl_t::*;
use crate::kv::volatile::volatilespec_t::*;
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

    impl<K, H, P> DurableKvStoreViewEntry<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange
    {
        pub closed spec fn key(self) -> K
        {
            self.key
        }

        pub closed spec fn header(self) -> H
        {
            self.header
        }

        pub closed spec fn pages(self) -> Seq<P>
        {
            self.pages
        }
    }

    pub struct DurableKvStoreView<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        pub contents: Seq<Option<DurableKvStoreViewEntry<K, H, P>>>
    }

    impl<K, H, P> DurableKvStoreView<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        pub closed spec fn spec_index(self, idx: int) -> Option<DurableKvStoreViewEntry<K, H, P>>
        {
            self.contents[idx]
        }

        pub closed spec fn empty(self) -> bool
        {
            forall |i| 0 <= i < self.contents.len() ==>
                self.contents[i].is_None()
        }
    }

    impl<K, H, P> DurableKvStoreView<K, H, P>
    where
        K: Hash + Eq,
        P: LogicalRange,
    {
        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub closed spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            ||| (self.empty() && volatile_index.empty())
            ||| forall |k: K| volatile_index.contains_key(k) <==>
                {
                    let index = volatile_index[k];
                    match index {
                        Some(index) => {
                            let entry = self.contents[index as int];
                            match entry {
                                Some(entry) => entry.key == k,
                                None => false
                            }
                        }
                        None => false
                    }

                }

        }
    }

    pub proof fn lemma_empty_index_matches_empty_store<K, H, P>(durable_store: DurableKvStoreView<K, H, P>, volatile_index: VolatileKvIndexView<K>)
        where
            K: Hash + Eq,
            P: LogicalRange,
        requires
            durable_store.empty(),
            volatile_index.empty(),
        ensures
            durable_store.matches_volatile_index(volatile_index)
    {}
}
