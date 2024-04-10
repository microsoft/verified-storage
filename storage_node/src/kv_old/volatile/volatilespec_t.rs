//! A `VolatileKvIndex` represents the volatile component of a `KvStore`.
//! Currently, it maps each key to 1) the physical offset of the metadata header associated
//! with that key in the header store, and 2) a list of physical offsets of list entries
//! associated with that key.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::kvimpl_t::*;
use std::hash::Hash;

verus! {
    pub struct VolatileKvIndexEntry
    {
        pub metadata_offset: int, // the physical offset of the metadata header associated with this key
        pub list_entry_offsets: Seq<int>, // the physical offset of list entries associated with this key, in order
    }

    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub contents: Map<K, VolatileKvIndexEntry>,
    }

    impl<K> VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub closed spec fn spec_index(&self, key: K) -> Option<VolatileKvIndexEntry>
        {
            if self.contents.dom().contains(key) {
                Some(self.contents.index(key))
            } else {
                None
            }
        }

        pub open spec fn contains_key(&self, key: K) -> bool
        {
            self.contents.contains_key(key)
        }

        pub open spec fn insert_metadata_offset(&self, key: K, metadata_offset: int) -> Self
        {
            Self { contents: self.contents.insert(key, VolatileKvIndexEntry { metadata_offset, list_entry_offsets: Seq::empty() }) }
        }

        pub closed spec fn append_entry_offset(&self, key: K, entry_offset: int) -> Self
        {
            let current_entry = self.contents[key];
            Self { contents: self.contents.insert(
                key,
                VolatileKvIndexEntry {
                    metadata_offset: current_entry.metadata_offset,
                    list_entry_offsets: current_entry.list_entry_offsets.push(entry_offset)
                })
            }
        }

        pub closed spec fn remove(&self, key: K) -> Self
        {
            Self { contents: self.contents.remove(key) }
        }

        pub open spec fn empty(self) -> bool {
            &&& self.contents.is_empty()
            &&& self.contents.dom().finite()
        }

        pub open spec fn keys(self) -> Set<K> {
            self.contents.dom()
        }
    }


}
