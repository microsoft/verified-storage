#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::paged_kv::pagedkvimpl_t::*;
use crate::paged_kv::volatile::volatilespec_t::*;
use std::hash::Hash;

verus! {
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
