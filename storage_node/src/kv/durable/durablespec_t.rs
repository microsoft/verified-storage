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

    pub struct DurableKvStoreListNode<L>
    {
        list: Seq<L>,
        offset_of_first_entry: int // TODO: what exactly does this represent...?
    }


    // TODO: need a way to order these
    pub struct DurableKvStoreList<L>
    {
        pub list: Map<int, DurableKvStoreListNode<L>>,
        pub num_entries: int
    }

    impl<L> DurableKvStoreList<L>
    {
        pub open spec fn spec_index(self, idx: int) -> Option<L>
        {
            if self.list.contains_key(idx) {
                Some(self.list[idx])
            } else {
                None
            }
        }

        pub open spec fn len(self) -> int
        {
            self.num_entries
        }

        pub open spec fn empty() -> Self
        {
            DurableKvStoreList {
                list: Map::empty(),
                num_entries: 0
            }
        }

        pub open spec fn view_as_seq(self) -> Seq<L>
        {

        }

    }

    pub struct DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub key: K,
        pub item: I,
        pub list: DurableKvStoreList<L>,

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

        pub open spec fn pages(self) -> DurableKvStoreList<L>
        {
            self.list
        }
    }

    pub struct DurableKvStoreView<K, I, L, E>
    where
        K: Hash + Eq + std::fmt::Debug,
        I: Item<K>,
        E: std::fmt::Debug
    {
        pub contents: Map<int, DurableKvStoreViewEntry<K, I, L>>,
        pub _phantom: Option<E>
    }

    impl<K, I, L, E> DurableKvStoreView<K, I, L, E>
    where
        K: Hash + Eq + std::fmt::Debug,
        I: Item<K>,
        E: std::fmt::Debug
    {
        pub open spec fn spec_index(self, idx: int) -> Option<DurableKvStoreViewEntry<K, I, L>>
        {
            if self.contents.contains_key(idx) {
                Some(self.contents[idx])
            } else {
                None
            }
        }

        pub closed spec fn empty(self) -> bool
        {
            self.contents.is_empty()
        }

        pub open spec fn len(self) -> nat
        {
            self.contents.len()
        }

        pub open spec fn create(self, offset: int, item: I) -> Result<Self, KvError<K, E>>
        {
            if self.contents.contains_key(offset) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(
                    Self {
                        contents: self.contents.insert(
                            offset,
                            DurableKvStoreViewEntry {
                                key: item.spec_key(),
                                item,
                                list: DurableKvStoreList::empty()
                            }
                        ),
                        _phantom: None
                    }
                )
            }

        }

        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub open spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            ||| (self.empty() && volatile_index.empty())
            ||| forall |k: K| volatile_index.contains_key(k) <==>
                {
                    let index = volatile_index[k];
                    match index {
                        Some(index) => {
                            let entry = self[index.metadata_offset];
                            match entry {
                                Some(entry) => {
                                    &&& entry.key() == k
                                    // &&& forall |i: int| #![auto] 0 <= i < entry.pages().len() ==> {
                                    //         entry.pages()[i].0 == index.list_entry_offsets[i]
                                    // }
                                }
                                None => false
                            }
                        }
                        None => false
                    }

                }
        }
    }
}
