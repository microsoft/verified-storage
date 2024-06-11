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
    pub struct VolatileKvListEntryLocation
    {
        pub list_node_addr: int,
        pub offset_within_list_node: int,
    }
    
    pub struct VolatileKvIndexEntry
    {
        pub item_offset: int,  // the physical offset of the metadata header associated with this key
        pub logical_head: int, // the logical index of the head of the list
        pub logical_tail: int, // the logical index of the tail of the list
        pub entry_locations: Seq<VolatileKvListEntryLocation>,
                             // the locations of the list entries, starting at the logical head and
                             // extending at least to the tail (and possibly beyond the tail to
                             // reflect free entries)
    }

    #[verifier::reject_recursive_types(K)]
    pub struct VolatileKvIndexView<K>
    where
        K: Hash + Eq,
    {
        pub contents: Map<K, VolatileKvIndexEntry>,
        pub list_entries_per_node: int
    }

    impl<K> VolatileKvIndexView<K>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(self, key: K) -> Option<VolatileKvIndexEntry>
        {
            if self.contents.contains_key(key) {
                Some(self.contents.index(key))
            } else {
                None
            }
        }

        pub open spec fn wf(self) -> bool
        {
            &&& 0 < self.list_entries_per_node
            &&& forall |k| self.contains_key(k) ==> {
                   let entry = self.contents[k];
                   &&& 0 <= entry.logical_head <= entry.logical_tail
                   &&& entry.entry_locations.len() >= entry.logical_head - entry.logical_tail
               }
        }

        pub open spec fn contains_key(self, key: K) -> bool
        {
            self[key] is Some
        }

        pub open spec fn len(self) -> int
        {
            self.contents.len() as int
        }

        pub open spec fn insert_item_offset(self, key: K, item_offset: int) -> Self
            recommends
                self.wf(),
                !self.contains_key(key),
        {
            Self {
                contents: self.contents.insert(
                        key,
                        VolatileKvIndexEntry {
                            item_offset,
                            logical_head: 0,
                            logical_tail: 0,
                            entry_locations: Seq::empty(),
                        }
                    ),
                ..self
            }
        }

        // adds a new list node's offset to the volatile index. In order to call this, we must have first
        // allocated a new node and inserted an entry into it in the durable store, so we insert
        // the node into the index with `num_entries` set to 1.
        pub open spec fn append_list_node_addr(self, key: K, list_node_addr: int) -> Self
            recommends
                self.wf(),
                self.contains_key(key),
        {
            let entry = self.contents[key];
            let new_locations = Seq::new(self.list_entries_per_node as nat, |i| {
                VolatileKvListEntryLocation {
                    list_node_addr,
                    offset_within_list_node: i,
                }
            });
            Self {
                contents: self.contents.insert(
                    key,
                    VolatileKvIndexEntry {
                        entry_locations: entry.entry_locations + new_locations,
                        ..entry
                    }),
                ..self
            }
        }


        // Returns the address of the list node that contains the specified logical list index,
        // and which entry in that list node corresponds to that logical index.
        pub open spec fn get_list_entry_location<E>(self, key: K, index: int)
                                                    -> Result<VolatileKvListEntryLocation, KvError<K,E>>
            where
                E: std::fmt::Debug
            recommends
                self.wf()
        {
            if !self.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let entry = self.contents[key];
                if index < entry.logical_head || index >= entry.logical_tail {
                    Err(KvError::IndexOutOfRange)
                }
                else {
                    Ok(entry.entry_locations[index - entry.logical_head])
                }
            }
        }

        // returns the length of the list associated with this key
        pub open spec(checked) fn list_len(self, key: K) -> int
            recommends
                self.wf(),
                self.contains_key(key),
        {
            let entry = self.contents[key];
            entry.logical_tail - entry.logical_head
        }

        // Updates the index to reflect that an entry has been appended to the end of the list.
        // It doesn't actually matter what the entry is -- we just need to update the index
        // to reflect that something new has been added
        pub open spec fn append_to_list<E>(self, key: K) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
            recommends
                self.wf(),
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            }
            else {
                let entry = self.contents[key];
                if entry.entry_locations.len() <= entry.logical_tail - entry.logical_head {
                    Err(KvError::OutOfSpace)
                }
                else {
                    Ok(Self {
                        contents: self.contents.insert(
                            key,
                            VolatileKvIndexEntry {
                                logical_tail: entry.logical_tail + 1,
                                ..entry
                            }),
                        ..self
                    })
                }
            }
        }

        // TODO: clean this up/split into multiple spec functions
        pub open spec fn trim_list<E>(self, key: K, trim_length: int) -> Result<Self, KvError<K, E>>
            where
                E: std::fmt::Debug
            recommends
                self.wf(),
        {
            if !self.contents.contains_key(key) {
                Err(KvError::KeyNotFound)
            } else {
                let entry = self.contents[key];
                if entry.logical_head > trim_length {
                    Err(KvError::IndexOutOfRange)
                }
                else if entry.logical_tail < trim_length {
                    Err(KvError::IndexOutOfRange)
                }
                else {
                    Ok(Self{
                        contents: self.contents.insert(
                            key,
                            VolatileKvIndexEntry {
                                logical_head: trim_length,
                                entry_locations: entry.entry_locations.skip(trim_length - entry.logical_head),
                                ..entry
                            }),
                        ..self
                    })
                }
            }
        }

        pub closed spec fn remove(self, key: K) -> Self
        {
            Self {
                contents: self.contents.remove(key),
                ..self
            }
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
