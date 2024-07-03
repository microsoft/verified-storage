//! A `DurableKvStore` represents the durable components of a `KvStore`. It is generic
//! to allow for different PM abstractions, persistent layouts, etc.
//! It should refine an array where each element optionally contains a key, a item,
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

// TODO: is it safe for the fields of the structs in this file to be pub?

verus! {
    // pub struct DurableKvStoreList<L>
    // {
    //     pub list: Seq<L>,
    //     // pub node_offset_map: Map<int, int> // maps nodes to the first logical list index they contain
    // }

    // impl<L> DurableKvStoreList<L>
    // {
    //     pub open spec fn spec_index(self, idx: int) -> Option<L>
    //     {
    //         if idx < self.list.len() {
    //             Some(self.list[idx])
    //         } else {
    //             None
    //         }
    //     }

    //     // pub open spec fn offset_index(self, offset: int) -> Option<int>
    //     // {
    //     //     if self.node_offset_map.contains_key(offset) {
    //     //         Some(self.node_offset_map[offset])
    //     //     } else {
    //     //         None
    //     //     }
    //     // }

    //     pub open spec fn len(self) -> int
    //     {
    //         self.list.len() as int
    //     }

    //     pub open spec fn empty() -> Self
    //     {
    //         DurableKvStoreList {
    //             list: Seq::empty(),
    //             // node_offset_map: Map::empty(),
    //         }
    //     }
    // }

    pub struct DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub key: K,
        pub item: I,
        pub list: Seq<L>,
    }

    // TODO: remove since the fields are public
    impl<K, I, L> DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub open spec fn key(self) -> K
        {
            self.key
        }

        pub open spec fn item(self) -> I
        {
            self.item
        }

        pub open spec fn list(self) -> Seq<L>
        {
            self.list
        }
    }

    pub struct DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub contents: Map<int, DurableKvStoreViewEntry<K, I, L>>,
    }

    impl<K, I, L> DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(self, idx: int) -> Option<DurableKvStoreViewEntry<K, I, L>>
        {
            if self.contents.contains_key(idx) {
                Some(self.contents[idx])
            } else {
                None
            }
        }

        pub open spec fn contains_key(self, idx: int) -> bool
        {
            self[idx] is Some
        }

        pub open spec fn empty(self) -> bool
        {
            self.contents.is_empty()
        }

        pub open spec fn len(self) -> nat
        {
            self.contents.len()
        }

        pub open spec fn initialize() -> Self 
        {
            Self {
                contents: Map::empty(),
            }
        }

        pub open spec fn create(self, offset: int, key: K, item: I) -> Result<Self, KvError<K>>
        {
            if self.contents.contains_key(offset) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(
                    Self {
                        contents: self.contents.insert(
                            offset,
                            DurableKvStoreViewEntry {
                                key,
                                item,
                                list: Seq::empty()
                            }
                        ),
                    }
                )
            }
        }

        pub open spec fn valid(self) -> bool
        {
            &&& self.contents.dom().finite()
        }

        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub open spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            &&& self.len() == volatile_index.contents.len()
            &&& volatile_index.valid()
            &&& self.valid()
            // all keys in the volatile index are stored at the indexed offset in the durable store
            &&& forall |k: K| #![auto] volatile_index.contains_key(k) ==> {
                    let indexed_offset = volatile_index[k].unwrap().header_addr;
                    &&& self.contents.contains_key(indexed_offset)
                    &&& self.contents[indexed_offset].key == k
                }
            // all offsets in the durable store have a corresponding entry in the volatile index
            &&& forall |i: int| #![auto] self.contains_key(i) ==> {
                &&& volatile_index.contains_key(self.contents[i].key)
                &&& volatile_index[self.contents[i].key].unwrap().header_addr == i
            }
        }
    }
}
