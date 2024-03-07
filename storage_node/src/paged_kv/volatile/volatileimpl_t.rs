//! A `VolatileKvIndex` represents the volatile component of a `PagedKv`.
//! Its main job is to map keys to physical locations within the `DurableKvStore`
//! to facilitate lookups.
//!
//! I think this should refine a simple map of keys to indexes in the durable component,
//! but not sure exactly how I think the spec should look yet.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::interface_t::*;
use std::hash::Hash;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        contents: Map<K, usize>
    }

    impl<K> VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub closed spec fn index(&self, key: K) -> usize
        {
            self.contents.index(key)
        }

        pub closed spec fn contains_key(&self, key: K) -> bool
        {
            self.contents.contains_key(key)
        }
    }

    pub trait VolatileKvIndex<K, E> : Sized
    where
        K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        spec fn view(&self) -> VolatileKvIndexView<K>;

        fn new(
            kvstore_id: u128,
            max_keys: usize,
        ) -> Result<Self, PagedKvError<K, E>>;
    }
}
