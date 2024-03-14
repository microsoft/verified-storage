#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::durable::durablespec_t::*;
use crate::paged_kv::pagedkvimpl_t::*;
use crate::paged_kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
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
        ) -> (result: Result<Self, PagedKvError<K, E>>)
            ensures
                match(result) {
                    Ok(durable_store) => {
                        &&& durable_store@.empty()
                    }
                    Err(_) => true // TODO
                };
    }
}
