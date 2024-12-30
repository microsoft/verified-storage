//! This file contains the unverified specification for the high-level KV store.
//! We also define the crash-consistency-related TrustedKvPermission structure
//! here.
//!
//! This file should be audited for correctness.

#![allow(unused_imports)]
// #![verus::trusted]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;

verus! {

#[derive(Debug)]
pub enum KvError<K>
where
    K: std::fmt::Debug,
{
    NotImplemented,
    InvalidParameter,
    InternalError, // TODO: reason
    WrongKvStoreId{ requested_id: u128, actual_id: u128 },
    KeyNotFound,
    KeyAlreadyExists,
    InvalidKey{ key: K },
    IndexOutOfRange,
    KeySizeTooBig,
    ItemSizeTooBig,
    ListElementSizeTooBig,
    TooFewKeys,
    TooManyListEntriesPerNode,
    TooManyKeys,
    TooManyListNodes,
    RegionTooSmall { required: usize, actual: usize },
    TooFewRegions { required: usize, actual: usize },
    TooManyRegions { required: usize, actual: usize },
    LogAreaTooSmall { required: usize, actual: usize },
    OutOfSpace,
    InvalidPersistentMemoryRegionProvided, // TODO: reason
    CRCMismatch,
    InvalidItemTableHeader,
    InvalidListMetadata,
    InvalidListRegionMetadata,
    EntryIsValid,
    EntryIsNotValid,
    InvalidLogEntryType,
    NoCurrentTransaction,
    PmemErr { pmem_err: PmemError },
}

/// An `AbstractKvStoreState` is an abstraction of
/// an entire `KvStoreStore`.
/// TODO: Should this be generic over the key/header/page
/// types used in the kv store, or over their views?
#[verifier::reject_recursive_types(K)]
pub struct AbstractKvStoreState<K, I, L>
{
    pub id: u128,
    pub contents: Map<K, (I, Seq<L>)>,
}

impl<K, I, L> AbstractKvStoreState<K, I, L>
where
    K: std::fmt::Debug,
{
    pub open spec fn init(id: u128) -> Self
    {
        Self{ id, contents: Map::<K, (I, Seq<L>)>::empty() }
    }

    pub open spec fn empty(self) -> bool
    {
        self.contents.is_empty()
    }

    pub open spec fn contains_key(&self, key: K) -> bool
    {
        self.contents.contains_key(key)
    }

    pub open spec fn spec_index(self, key: K) -> Option<(I, Seq<L>)>
    {
        if self.contents.contains_key(key) {
            Some(self.contents[key])
        } else {
            None
        }
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

    pub open spec fn read_item(self, key: K) -> Result<I, KvError<K>>
    {
        if self.contents.contains_key(key) {
            Ok(self.contents[key].0)
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn read_item_and_list(self, key: K) -> Result<(I, Seq<L>), KvError<K>>
    {
        if self.contents.contains_key(key) {
            Ok(self.contents[key])
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    // pub open spec fn read_list_entry_at_index(self, key: K, idx: int) -> Result<L, KvError<K>>
    // {
    //     if self.contents.contains_key(key) {
    //         let (offset, list) = self.contents[key];
    //         if list.len() > idx {
    //             Ok(list[idx])
    //         } else {
    //             Err(KvError::IndexOutOfRange)
    //         }
    //     } else {
    //         Err(KvError::KeyNotFound)
    //     }
    // }

    pub open spec fn update_item(self, key: K, new_item: I) -> Result<Self, KvError<K>>
    {
        let val = self.read_item_and_list(key);
        match val {
            Ok((old_item, pages)) => {
                Ok(Self {
                    id: self.id,
                    contents: self.contents.insert(key, (new_item, pages)),
                })
            },
            Err(e) => Err(e),
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

    // pub open spec fn append_to_list(self, key: K, new_list_entry: L) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (item, pages.push(new_list_entry))),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub open spec fn append_to_list_and_update_item(self, key: K, new_list_entry: L, new_item: I) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (new_item, pages.push(new_list_entry))),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub open spec fn update_list_entry_at_index(self, key: K, idx: usize, new_list_entry: L) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             let pages = pages.update(idx as int, new_list_entry);
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (item, pages)),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub open spec fn update_entry_at_index_and_item(self, key: K, idx: usize, new_list_entry: L, new_item: I) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             let pages = pages.update(idx as int, new_list_entry);
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (new_item, pages)),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub open spec fn trim_list(self, key: K, trim_length: int) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             let pages = pages.subrange(trim_length, pages.len() as int);
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (item, pages)),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub open spec fn trim_list_and_update_item(self, key: K, trim_length: int, new_item: I) -> Result<Self, KvError<K>>
    // {
    //     let result = self.read_item_and_list(key);
    //     match result {
    //         Some((item, pages)) => {
    //             let pages = pages.subrange(trim_length, pages.len() as int);
    //             Ok(Self {
    //                 id: self.id,
    //                 contents: self.contents.insert(key, (new_item, pages)),
    //             })
    //         }
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    pub open spec fn get_keys(self) -> Set<K>
    {
        self.contents.dom()
    }
}

#[verifier::reject_recursive_types(K)]
pub struct AbstractKvState<K, I, L>
{
    pub durable: AbstractKvStoreState<K, I, L>,
    pub tentative: AbstractKvStoreState<K, I, L>,
}

impl <K, I, L> AbstractKvState<K, I, L>
where
    K: Hash + Eq,
{
    pub open spec fn valid(self) -> bool
    {
        self.durable.id == self.tentative.id
    }

    pub open spec fn id(self) -> u128
    {
        self.durable.id
    }

    pub open spec fn abort(self) -> Self
    {
        Self{
            tentative: self.durable,
            ..self
        }
    }

    pub open spec fn commit(self) -> Self
    {
        Self{
            durable: self.tentative,
            ..self
        }
    }

    pub open spec fn constants_match(self, other: Self) -> bool
    {
        &&& self.durable.id == other.durable.id
        &&& self.tentative.id == other.tentative.id
    }
}

}
