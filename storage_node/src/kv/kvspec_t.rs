//! This file contains the unverified specification for the high-level KV store.
//! We also define the crash-consistency-related TrustedKvPermission structure
//! here.
//!
//! This file should be audited for correctness.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::wrpm_t::*;

use crate::kv::durable::durableimpl_v::*;
use crate::kv::durable::durablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvimpl_v::*;
use crate::kv::volatile::volatileimpl_v::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use std::hash::Hash;

verus! {

    // Since the durable part of the PagedKV is a list of PM regions,
    // we use Seq<Seq<u8>> to determine whether states are crash-consistent.
    pub struct TrustedKvPermission<PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool,
        _phantom:  Ghost<core::marker::PhantomData<(PM, K, I, L)>>
    }

    impl<PM, K, I, L> CheckPermission<Seq<Seq<u8>>> for TrustedKvPermission<PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    impl<PM, K, I, L> TrustedKvPermission<PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        // methods copied from multilogimpl_t and updated for PagedKV structures

        // This is one of two constructors for `TrustedKvPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        pub proof fn new_one_possibility(kv_id: u128, state: AbstractKvStoreState<K, I, L>) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state)
        {
            Self {
                is_state_allowable: |s| DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state),
                _phantom: Ghost(spec_phantom_data())
            }
        }

        // This is the second of two constructors for
        // `TrustedKvPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        pub proof fn new_two_possibilities(
            kv_id: u128,
            state1: AbstractKvStoreState<K, I, L>,
            state2: AbstractKvStoreState<K, I, L>
        ) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state1)
                    ||| DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state2)
                }
        {
            Self {
                is_state_allowable: |s| {
                    ||| DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state1)
                    ||| DurableKvStore::<PM, K, I, L>::recover_to_kv_state(s, kv_id) == Some(state2)
                },
                _phantom: Ghost(spec_phantom_data())
            }
        }

        // TODO: REMOVE THIS
        #[verifier::external_body]
        pub proof fn fake_kv_perm() -> (tracked perm: Self)
        {
            Self {
                is_state_allowable: |s| true,
                _phantom: Ghost(spec_phantom_data())
            }
        }

    }


    /// An `AbstractKvStoreState` is an abstraction of
    /// an entire `KvStoreStore`.
    /// TODO: Should this be generic over the key/header/page
    /// types used in the kv store, or over their views?
    #[verifier::reject_recursive_types(K)]
    pub struct AbstractKvStoreState<K, I, L>
    where
        K: Hash + Eq,
    {
        pub id: u128,
        pub contents: Map<K, (I, Seq<L>)>,
    }

    impl<K, I, L> AbstractKvStoreState<K, I, L>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(self, key: K) -> Option<(I, Seq<L>)>
        {
            if self.contents.contains_key(key) {
                Some(self.contents[key])
            } else {
                None
            }
        }

        pub open spec fn empty(self) -> bool
        {
            self.contents.is_empty()
        }

        pub open spec fn contains_key(&self, key: K) -> bool
        {
            self.contents.contains_key(key)
        }

        pub open spec fn construct_view_contents(
            volatile_store_state: VolatileKvIndexView<K>,
            durable_store_state: DurableKvStoreView<K, I, L>
        ) -> Map<K, (I, Seq<L>)> {
            Map::new(
                |k| { volatile_store_state.contains_key(k) },
                |k| {
                    let index_entry = volatile_store_state[k].unwrap();
                    let durable_entry = durable_store_state[index_entry.item_offset].unwrap();
                    (durable_entry.item(), durable_entry.list().list)
                }
            )
        }

        pub open spec fn create(self, key: K, item: I) -> Result<Self, KvError<K>>
        {
            if self.contents.contains_key(key) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(Self {
                    id: self.id,
                    contents: self.contents.insert(key, (item, Seq::empty())),
                })
            }

        }

        pub open spec fn read_item_and_list(self, key: K) -> Option<(I, Seq<L>)>
        {
            if self.contents.contains_key(key) {
                Some(self.contents[key])
            } else {
                None
            }
        }

        pub open spec fn read_list_entry_at_index(self, key: K, idx: int) -> Result<L, KvError<K>>
        {
            if self.contents.contains_key(key) {
                let (offset, list) = self.contents[key];
                if list.len() > idx {
                    Ok(list[idx])
                } else {
                    Err(KvError::IndexOutOfRange)
                }
            } else {
                Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn update_item(self, key: K, new_item: I) -> Result<Self, KvError<K>>
        {
            let val = self.read_item_and_list(key);
            match val {
                Some((old_item, pages)) => {
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_item, pages)),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }

        }

        pub open spec fn delete(self, key: K) -> Result<Self, KvError<K>>
        {
            if self.contents.contains_key(key) {
                Ok(Self {
                    id: self.id,
                    contents: self.contents.remove(key),
                })
            } else {
                Err(KvError::KeyNotFound)
            }

        }

        pub open spec fn append_to_list(self, key: K, new_list_entry: L) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (item, pages.push(new_list_entry))),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn append_to_list_and_update_item(self, key: K, new_list_entry: L, new_item: I) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_item, pages.push(new_list_entry))),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn update_list_entry_at_index(self, key: K, idx: usize, new_list_entry: L) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    let pages = pages.update(idx as int, new_list_entry);
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (item, pages)),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn update_entry_at_index_and_item(self, key: K, idx: usize, new_list_entry: L, new_item: I) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    let pages = pages.update(idx as int, new_list_entry);
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_item, pages)),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn trim_list(self, key: K, trim_length: int) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    let pages = pages.subrange(trim_length, pages.len() as int);
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (item, pages)),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn trim_list_and_update_item(self, key: K, trim_length: int, new_item: I) -> Result<Self, KvError<K>>
        {
            let result = self.read_item_and_list(key);
            match result {
                Some((item, pages)) => {
                    let pages = pages.subrange(trim_length, pages.len() as int);
                    Ok(Self {
                        id: self.id,
                        contents: self.contents.insert(key, (new_item, pages)),
                    })
                }
                None => Err(KvError::KeyNotFound)
            }
        }

        pub open spec fn get_keys(self) -> Set<K>
        {
            self.contents.dom()
        }
    }

}
