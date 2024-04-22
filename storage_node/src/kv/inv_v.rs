//! This file contains helper proofs and invariants about the state
//! of the high-level KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

use crate::kv::durable::durableimpl_v::*;
use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvimpl_v::*;
use crate::kv::kvspec_t::*;
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
    pub proof fn lemma_volatile_matches_durable_after_create<K, I, L, E>(
        old_durable_state: DurableKvStoreView<K, I, L, E>,
        old_volatile_state: VolatileKvIndexView<K>,
        offset: int,
        key: K,
        item: I
    )
        where
            K: Hash + Eq + std::fmt::Debug,
            I: Item<K>,
            E: std::fmt::Debug
        requires
            old_durable_state.matches_volatile_index(old_volatile_state),
            old_durable_state[offset] is None,
            old_volatile_state[key] is None,
            item.spec_key() == key,
        ensures
            ({
                let new_durable_state = old_durable_state.create(offset, item).unwrap();
                let new_volatile_state = old_volatile_state.insert_item_offset(key, offset);
                new_durable_state.matches_volatile_index(new_volatile_state)
            })
    {
        let new_durable_state = old_durable_state.create(offset, item).unwrap();
        let new_volatile_state = old_volatile_state.insert_item_offset(key, offset);

        assert(new_durable_state.contains_key(offset));
        assert(new_volatile_state.contains_key(key));
        assert(new_volatile_state[key].unwrap().item_offset == offset);
        assert(new_durable_state[offset].unwrap().key() == key);

        assert(old_durable_state.contents.submap_of(new_durable_state.contents));
        assert(old_volatile_state.contents.submap_of(new_volatile_state.contents));
        assert(new_durable_state.contents.dom() == old_durable_state.contents.dom().insert(offset));
        assert(new_volatile_state.contents.dom() == old_volatile_state.contents.dom().insert(key));

        assert forall |k: K| #![auto] new_volatile_state.contains_key(k) implies {
            exists |i: int| #![auto] {
                &&& new_durable_state.contains_key(i)
                &&& new_durable_state[i].unwrap().key() == k
                &&& new_volatile_state[k].unwrap().item_offset == i
            }
        } by {
            let index_entry = new_volatile_state[k].unwrap();
            if k != key {
                // k was in the old state; corresponding durable and volatile entries
                // are the same in the new and old states for both durable and volatile
                assert(old_volatile_state.contains_key(k));
                let i_witness = old_volatile_state[k].unwrap().item_offset;
                assert(new_volatile_state[k].unwrap().item_offset == i_witness);
                assert(old_durable_state.contains_key(i_witness));
                assert(new_durable_state.contains_key(i_witness));
            }
            // we have already established this for the k == key case
        }

        assert forall |i: int| #![auto] new_durable_state.contains_key(i) implies {
            exists |k: K| #![auto] {
                &&& new_volatile_state.contains_key(k)
                &&& new_durable_state[i].unwrap().key() == k
                &&& new_volatile_state[k].unwrap().item_offset == i
            }
        } by {
            let durable_entry = new_durable_state[i].unwrap();
            if i != offset {
                // i was in the old state; corresponding durable and volatile entries
                // are the same in the new and old states for both durable and volatile
                assert(old_durable_state.contains_key(i));
                let k_witness = old_durable_state[i].unwrap().key();
                assert(new_durable_state[i].unwrap().key() == k_witness);
                assert(old_volatile_state.contains_key(k_witness));
                assert(new_volatile_state.contains_key(k_witness));
            }
            // we have already established this for the i == offset case
        }

        assert(new_durable_state.matches_volatile_index(new_volatile_state));
    }
}
