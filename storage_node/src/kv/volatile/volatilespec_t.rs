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

use crate::kv::kvimpl_t::*;
use std::hash::Hash;

verus! {
    pub struct VolatileKvIndexEntry
    {
        pub metadata_offset: int,
        pub list_entry_offsets: Seq<int>,
    }

    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        contents: Map<K, VolatileKvIndexEntry>,
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

        pub closed spec fn contains_key(&self, key: K) -> bool
        {
            self.contents.contains_key(key)
        }

        pub closed spec fn insert_metadata_offset(&self, key: K, metadata_offset: int) -> Self
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

        pub closed spec fn empty(self) -> bool {
            self.contents == Map::<K, VolatileKvIndexEntry>::empty()
        }

        pub closed spec fn keys(self) -> Seq<K> {
            self.contents.dom().to_seq()
        }
    }


}
