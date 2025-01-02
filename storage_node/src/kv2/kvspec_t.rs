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
    IndexOutOfRange{ upper_bound: usize },
    KeySizeTooSmall,
    KeySizeTooBig,
    ItemSizeTooBig,
    ListEntrySizeTooBig,
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
    LogicalRangeHasBeenTrimmed{ logical_trim_position: usize },
    LogicalRangeHasBeenPartiallyTrimmed{ logical_trim_position: usize },
    LogicalRangePartiallyBeyondEOF{ end_of_valid_range: usize },
    LogicalRangeBeyondEOF{ end_of_valid_range: usize },
    PageOutOfLogicalRangeOrder{ end_of_valid_range: usize },
    PageLeavesLogicalRangeGap{ end_of_valid_range: usize },
    LogicalRangeUpdateNotAllowed{ old_start: usize, old_end: usize, new_start: usize, new_end: usize },
    PmemErr { pmem_err: PmemError },
}

pub enum LogicalRangeGapsPolicy {
    LogicalRangeGapsForbidden,
    LogicalRangeGapsPermitted,
}

pub struct SetupParameters {
    pub kvstore_id: u128,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub num_keys: u64,
    pub num_list_entries_per_block: u64,
    pub num_list_blocks: u64,
    pub num_lists_to_cache: u64,
}

impl SetupParameters {
    pub open spec fn valid(self) -> bool
    {
        &&& 0 < self.num_keys
        &&& 0 < self.num_list_entries_per_block
        &&& 0 < self.num_list_blocks
        &&& 0 < self.num_lists_to_cache
    }
}

// The page type must satisfy the `LogicalRange` trait, giving it a
// logical range with a `start` and `end`.
pub trait LogicalRange {
    spec fn spec_start(&self) -> usize;
    spec fn spec_end(&self) -> usize;

    #[verifier::when_used_as_spec(spec_start)]
    fn start(&self) -> usize;
    #[verifier::when_used_as_spec(spec_end)]
    fn end(&self) -> usize;
}

pub open spec fn end_of_range<L>(list_entries: Seq<L>) -> usize
    where
        L: LogicalRange
{
    if list_entries.len() == 0 {
        0
    }
    else {
        list_entries.last().end()
    }
}

/// An `AtomicKvStore` is an abstraction of an atomic key/value
/// store, i.e., one that doesn't support tentative operations,
/// aborts, and commits.
/// TODO: Should this be generic over the key/header/page
/// types used in the kv store, or over their views?
#[verifier::reject_recursive_types(K)]
pub struct AtomicKvStore<K, I, L>
{
    pub id: u128,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub contents: Map<K, (I, Seq<L>)>,
}

impl<K, I, L> AtomicKvStore<K, I, L>
where
    K: std::fmt::Debug,
    L: LogicalRange,
{
    pub open spec fn init(id: u128, logical_range_gaps_policy: LogicalRangeGapsPolicy) -> Self
    {
        Self{ id, logical_range_gaps_policy, contents: Map::<K, (I, Seq<L>)>::empty() }
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
                contents: self.contents.insert(key, (item, Seq::empty())),
                ..self
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

    pub open spec fn read_list_entry_at_index(self, key: K, idx: nat) -> Result<L, KvError<K>>
    {
        if self.contents.contains_key(key) {
            let (offset, list) = self.contents[key];
            if idx < list.len() {
                Ok(list[idx as int])
            } else {
                Err(KvError::IndexOutOfRange{ upper_bound: list.len() as usize })
            }
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn update_item(self, key: K, new_item: I) -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((old_item, pages)) => {
                Ok(Self {
                    contents: self.contents.insert(key, (new_item, pages)),
                    ..self
                })
            },
            Err(e) => Err(e),
        }

    }

    pub open spec fn delete(self, key: K) -> Result<Self, KvError<K>>
    {
        if self.contents.contains_key(key) {
            Ok(Self {
                contents: self.contents.remove(key),
                ..self
            })
        } else {
            Err(KvError::KeyNotFound)
        }

    }

    pub open spec fn append_to_list(self, key: K, new_list_entry: L) -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) => {
                let end_of_valid_range = end_of_range(list_entries);
                if new_list_entry.start() < end_of_valid_range {
                    Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range })
                }
                else if {
                    &&& self.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_entry.start() > end_of_valid_range
                } {
                    Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range })
                }
                else {
                    Ok(Self {
                        contents: self.contents.insert(key, (item, list_entries.push(new_list_entry))),
                        ..self
                    })
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn append_to_list_and_update_item(self, key: K, new_list_entry: L, new_item: I)
                                                    -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) => {
                let end_of_valid_range = end_of_range(list_entries);
                if new_list_entry.start() < end_of_valid_range {
                    Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range })
                }
                else if {
                    &&& self.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_entry.start() > end_of_valid_range
                } {
                    Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range })
                }
                else {
                    Ok(Self {
                        contents: self.contents.insert(key, (new_item, list_entries.push(new_list_entry))),
                        ..self
                    })
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn update_list_entry_at_index(self, key: K, idx: nat, new_list_entry: L) -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) =>
                if idx >= list_entries.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_entries.len() as usize })
                }
                else {
                    let old_list_entry = list_entries[idx as int];
                    if old_list_entry.start() != new_list_entry.start() || old_list_entry.end() != new_list_entry.end() {
                        Err(KvError::LogicalRangeUpdateNotAllowed{ old_start: old_list_entry.start(),
                                                                   old_end: old_list_entry.end(),
                                                                   new_start: new_list_entry.start(),
                                                                   new_end: new_list_entry.end() })
                    }
                    else {
                        let new_list_entries = list_entries.update(idx as int, new_list_entry);
                        Ok(Self {
                            contents: self.contents.insert(key, (item, new_list_entries)),
                            ..self
                        })
                    }
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn update_list_entry_at_index_and_item(self, key: K, idx: nat, new_list_entry: L, new_item: I)
                                                         -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) => {
                if idx >= list_entries.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_entries.len() as usize })
                }
                else {
                    let old_list_entry = list_entries[idx as int];
                    if old_list_entry.start() != new_list_entry.start() || old_list_entry.end() != new_list_entry.end() {
                        Err(KvError::LogicalRangeUpdateNotAllowed{ old_start: old_list_entry.start(),
                                                                   old_end: old_list_entry.end(),
                                                                   new_start: new_list_entry.start(),
                                                                   new_end: new_list_entry.end() })
                    }
                    else {
                        let new_list_entries = list_entries.update(idx as int, new_list_entry);
                        Ok(Self {
                            contents: self.contents.insert(key, (new_item, new_list_entries)),
                            ..self
                        })
                    }
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn trim_list(self, key: K, trim_length: nat) -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) =>
                if trim_length > list_entries.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_entries.len() as usize })
                }
                else {
                    let new_list_entries = list_entries.subrange(trim_length as int, list_entries.len() as int);
                    Ok(Self {
                        contents: self.contents.insert(key, (item, list_entries)),
                        ..self
                    })
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn trim_list_and_update_item(self, key: K, trim_length: nat, new_item: I) -> Result<Self, KvError<K>>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_entries)) =>
                if trim_length > list_entries.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_entries.len() as usize })
                }
                else {
                    let new_list_entries = list_entries.subrange(trim_length as int, list_entries.len() as int);
                    Ok(Self {
                        contents: self.contents.insert(key, (new_item, list_entries)),
                        ..self
                    })
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn get_keys(self) -> Set<K>
    {
        self.contents.dom()
    }
}

#[verifier::reject_recursive_types(K)]
pub struct KvStoreView<K, I, L>
{
    pub id: u128,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub pm_constants: PersistentMemoryConstants,
    pub durable: AtomicKvStore<K, I, L>,
    pub tentative: AtomicKvStore<K, I, L>,
}

impl <K, I, L> KvStoreView<K, I, L>
where
    K: Hash + Eq,
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.id == self.durable.id == self.tentative.id
        &&& self.logical_range_gaps_policy == self.durable.logical_range_gaps_policy
        &&& self.logical_range_gaps_policy == self.tentative.logical_range_gaps_policy
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
        &&& self.valid()
        &&& other.valid()
        &&& self.id == other.id
        &&& self.logical_range_gaps_policy == other.logical_range_gaps_policy
        &&& self.pm_constants == other.pm_constants
    }
}

}
