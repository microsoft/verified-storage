//! This file contains helper proofs and invariants about the state
//! of the high-level KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;

use crate::kv::durable::durableimpl_v::*;
use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvimpl_v::*;
use crate::kv::volatile::volatileimpl_v::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
    pub proof fn lemma_empty_index_matches_empty_store<K, I, L, E>(durable_store: DurableKvStoreView<K, I, L, E>, volatile_index: VolatileKvIndexView<K>)
        where
            K: Hash + Eq + std::fmt::Debug,
            I: Item<K>,
            E: std::fmt::Debug
        requires
            durable_store.empty(),
            volatile_index.empty(),
        ensures
            durable_store.matches_volatile_index(volatile_index)
    {}

    pub proof fn lemma_empty_map_contains_no_keys<K, V>(map: Map<K, V>)
        requires
            map.is_empty(),
            map.dom().finite(),
        ensures
            forall |k: K| !map.contains_key(k)
    {}
}
