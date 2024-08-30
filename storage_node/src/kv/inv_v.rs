//! This file contains helper proofs and invariants about the state
//! of the high-level KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

use crate::kv::durable::durableimpl_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvimpl_v::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatileimpl_v::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {
    pub proof fn lemma_empty_index_matches_empty_store<K, I, L>(durable_store: DurableKvStoreView<K, I, L>, volatile_index: VolatileKvIndexView<K>)
        where
            K: Hash + Eq + std::fmt::Debug,
        requires
            durable_store.empty(),
            durable_store.valid(),
            durable_store.contents.dom().finite(),
            volatile_index.empty(),
        ensures
            durable_store.matches_volatile_index(volatile_index)
    {
        assert(durable_store.contents.is_empty());
        assert(durable_store.contents.dom().is_empty());
        lemma_empty_map_contains_no_keys(durable_store.contents);
    }

    pub proof fn lemma_empty_map_contains_no_keys<K, V>(map: Map<K, V>)
        requires
            map.is_empty(),
            map.dom().finite(),
        ensures
            forall |k: K| !map.contains_key(k)
    {}

    /// This lemma proves that, given a durable state and a volatile state that matches it
    /// (i.e., the durable and volatile states are the same size, the volatile index maps
    /// all keys to an offset with the corresponding durable entry and the durable store's
    /// entries correspond to the volatile index), then after creating a new entry in each
    /// using the same offset, key, and item, the durable and volatile states still match.
    pub proof fn lemma_volatile_matches_durable_after_create<K, I, L>(
        old_durable_state: DurableKvStoreView<K, I, L>,
        old_volatile_index: VolatileKvIndexView<K>,
        offset: int,
        key: K,
        item: I
    )
        where
            K: Hash + Eq + std::fmt::Debug,
        requires
            old_volatile_index.valid(),
            old_durable_state.matches_volatile_index(old_volatile_index),
            old_durable_state[offset] is None,
            old_volatile_index[key] is None,
        ensures
            ({
                let new_durable_state = old_durable_state.create(offset, key, item).unwrap();
                let new_volatile_index = old_volatile_index.insert_key(key, offset);
                new_durable_state.matches_volatile_index(new_volatile_index)
            })
    {
        let new_durable_state = old_durable_state.create(offset, key, item).unwrap();
        let new_volatile_index = old_volatile_index.insert_key(key, offset);

        assert forall |k: K| #[trigger] new_volatile_index.contains_key(k) implies {
            let indexed_offset = new_volatile_index[k].unwrap().header_addr;
            &&& new_durable_state.contains_key(indexed_offset)
            &&& new_durable_state[indexed_offset].unwrap().key == k
        } by {
            assert(old_volatile_index.contains_key(k) <==> k != key);
        }

        assert forall |i: int| #[trigger] new_durable_state.contains_key(i) implies {
                &&& new_volatile_index.contains_key(new_durable_state[i].unwrap().key)
                &&& new_volatile_index[new_durable_state[i].unwrap().key].unwrap().header_addr == i
                } by {
            assert(old_durable_state.contains_key(i) <==> new_durable_state[i].unwrap().key != key);
        }
    }
}
