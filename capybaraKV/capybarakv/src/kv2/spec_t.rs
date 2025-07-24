//! This file contains the unverified specification for the high-level KV store.
//!
//! This file should be audited for correctness.

#![allow(unused_imports)]
#![cfg_attr(verus_keep_ghost, verus::trusted)]
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {

#[derive(Debug)]
pub enum KvError
{
    NotImplemented,
    InvalidParameter,
    InternalError, // TODO: reason
    WrongKvStoreId{ requested_id: u128, actual_id: u128 },
    KeyNotFound,
    KeyAlreadyExists,
    InvalidKey,
    IndexOutOfRange{ upper_bound: usize },
    KeySizeTooSmall,
    KeySizeTooBig,
    ItemSizeTooBig,
    ListEntrySizeTooBig,
    TooFewKeys,
    TooManyListEntriesPerNode,
    TooManyKeys,
    TooManyListNodes,
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
    ListLengthWouldExceedUsizeMax,
}

pub enum LogicalRangeGapsPolicy {
    LogicalRangeGapsForbidden,
    LogicalRangeGapsPermitted,
}

pub struct SetupParameters {
    pub kvstore_id: u128,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub max_keys: u64,
    pub max_list_elements: u64,
    pub max_operations_per_transaction: u64,
}

impl SetupParameters {
    pub open spec fn valid(self) -> bool
    {
        &&& 0 < self.max_keys
        &&& 0 < self.max_list_elements
        &&& 0 < self.max_operations_per_transaction
    }
}

// The list-element type must satisfy the `LogicalRange` trait, giving
// it a logical range with a `start` and `end`. The KV store enforces
// that when appending a list element its `start` must be at least as
// large as the `end` of the current last element in that list. If one
// doesn't want such enforcement, one should just have `start` and
// `end` both always return `0`. If one wants even stricter
// enforcement, i.e., if one wants to require that the `start` of the
// appended element must be *exactly* equal to the `end` of the last
// element, one should initialize the KV store with the logical range
// gaps policy set to `LogicalRangeGapsForbidden`.

pub trait LogicalRange {
    spec fn spec_start(&self) -> usize;
    spec fn spec_end(&self) -> usize;

    #[verifier::when_used_as_spec(spec_start)]
    fn start(&self) -> (result: usize)
        ensures
            result == self.start(),
        ;
    #[verifier::when_used_as_spec(spec_end)]
    fn end(&self) -> (result: usize)
        ensures
            result == self.end()
        ;
}

pub open spec fn end_of_range<L>(list_elements: Seq<L>) -> usize
    where
        L: LogicalRange
{
    if list_elements.len() == 0 {
        0
    }
    else {
        list_elements.last().end()
    }
}

/// An `AtomicKvStore` is an abstraction of an atomic key/value
/// store, i.e., one that doesn't support tentative operations,
/// aborts, and commits.
#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct AtomicKvStore<K, I, L>
{
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub m: Map<K, (I, Seq<L>)>,
}

impl<K, I, L> AtomicKvStore<K, I, L>
where
    K: std::fmt::Debug,
    L: LogicalRange,
{
    pub open spec fn init(logical_range_gaps_policy: LogicalRangeGapsPolicy) -> Self
    {
        Self{
            logical_range_gaps_policy,
            m: Map::<K, (I, Seq<L>)>::empty()
        }
    }

    pub open spec fn empty(self) -> bool
    {
        self.m.is_empty()
    }

    pub open spec fn contains_key(&self, key: K) -> bool
    {
        self.m.contains_key(key)
    }

    pub open spec fn num_keys(&self) -> int
    {
        self.m.dom().len() as int
    }

    pub open spec fn num_list_elements(&self) -> int
    {
        self.m.dom().to_seq().fold_left(0, |total: int, k: K| total + self.m[k].1.len())
    }

    pub open spec fn spec_index(self, key: K) -> Option<(I, Seq<L>)>
    {
        if self.m.contains_key(key) {
            Some(self.m[key])
        } else {
            None
        }
    }

    pub open spec fn create(self, key: K, item: I) -> Result<Self, KvError>
    {
        if self.m.contains_key(key) {
            Err(KvError::KeyAlreadyExists)
        } else {
            Ok(Self {
                m: self.m.insert(key, (item, Seq::empty())),
                ..self
            })
        }
    }

    pub open spec fn read_item(self, key: K) -> Result<I, KvError>
    {
        if self.m.contains_key(key) {
            Ok(self.m[key].0)
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn read_item_and_list(self, key: K) -> Result<(I, Seq<L>), KvError>
    {
        if self.m.contains_key(key) {
            Ok(self.m[key])
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn read_list_element_at_index(self, key: K, idx: nat) -> Result<L, KvError>
    {
        if self.m.contains_key(key) {
            let (item, list) = self.m[key];
            if idx < list.len() {
                Ok(list[idx as int])
            } else {
                Err(KvError::IndexOutOfRange{ upper_bound: list.len() as usize })
            }
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn get_list_length(self, key: K) -> Result<nat, KvError>
    {
        if self.m.contains_key(key) {
            let (item, list) = self.m[key];
            Ok(list.len())
        } else {
            Err(KvError::KeyNotFound)
        }
    }

    pub open spec fn update_item(self, key: K, new_item: I) -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((old_item, pages)) => {
                Ok(Self {
                    m: self.m.insert(key, (new_item, pages)),
                    ..self
                })
            },
            Err(e) => Err(e),
        }

    }

    pub open spec fn delete(self, key: K) -> Result<Self, KvError>
    {
        if self.m.contains_key(key) {
            Ok(Self {
                m: self.m.remove(key),
                ..self
            })
        } else {
            Err(KvError::KeyNotFound)
        }

    }

    pub open spec fn append_to_list(self, key: K, new_list_element: L) -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) => {
                let end_of_valid_range = end_of_range(list_elements);
                if list_elements.len() >= usize::MAX {
                    Err(KvError::ListLengthWouldExceedUsizeMax)
                }
                else if new_list_element.start() < end_of_valid_range {
                    Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range })
                }
                else if {
                    &&& self.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_element.start() > end_of_valid_range
                } {
                    Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range })
                }
                else {
                    Ok(Self {
                        m: self.m.insert(key, (item, list_elements.push(new_list_element))),
                        ..self
                    })
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn append_to_list_and_update_item(self, key: K, new_list_element: L, new_item: I)
                                                    -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) => {
                let end_of_valid_range = end_of_range(list_elements);
                if list_elements.len() >= usize::MAX {
                    Err(KvError::ListLengthWouldExceedUsizeMax)
                }
                else if new_list_element.start() < end_of_valid_range {
                    Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range })
                }
                else if {
                    &&& self.logical_range_gaps_policy is LogicalRangeGapsForbidden
                    &&& new_list_element.start() > end_of_valid_range
                } {
                    Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range })
                }
                else {
                    Ok(Self {
                        m: self.m.insert(key, (new_item, list_elements.push(new_list_element))),
                        ..self
                    })
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn update_list_element_at_index(self, key: K, idx: nat, new_list_element: L) -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) =>
                if idx >= list_elements.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_elements.len() as usize })
                }
                else {
                    let old_list_element = list_elements[idx as int];
                    if old_list_element.start() != new_list_element.start() ||
                       old_list_element.end() != new_list_element.end() {
                        Err(KvError::LogicalRangeUpdateNotAllowed{ old_start: old_list_element.start(),
                                                                   old_end: old_list_element.end(),
                                                                   new_start: new_list_element.start(),
                                                                   new_end: new_list_element.end() })
                    }
                    else {
                        let new_list_elements = list_elements.update(idx as int, new_list_element);
                        Ok(Self {
                            m: self.m.insert(key, (item, new_list_elements)),
                            ..self
                        })
                    }
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn update_list_element_at_index_and_item(self, key: K, idx: nat, new_list_element: L, new_item: I)
                                                         -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) => {
                if idx >= list_elements.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_elements.len() as usize })
                }
                else {
                    let old_list_element = list_elements[idx as int];
                    if old_list_element.start() != new_list_element.start() || old_list_element.end() != new_list_element.end() {
                        Err(KvError::LogicalRangeUpdateNotAllowed{ old_start: old_list_element.start(),
                                                                   old_end: old_list_element.end(),
                                                                   new_start: new_list_element.start(),
                                                                   new_end: new_list_element.end() })
                    }
                    else {
                        let new_list_elements = list_elements.update(idx as int, new_list_element);
                        Ok(Self {
                            m: self.m.insert(key, (new_item, new_list_elements)),
                            ..self
                        })
                    }
                }
            },
            Err(e) => Err(e),
        }
    }

    pub open spec fn trim_list(self, key: K, trim_length: nat) -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) =>
                if trim_length > list_elements.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_elements.len() as usize })
                }
                else {
                    let new_list_elements = list_elements.skip(trim_length as int);
                    Ok(Self {
                        m: self.m.insert(key, (item, new_list_elements)),
                        ..self
                    })
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn trim_list_and_update_item(self, key: K, trim_length: nat, new_item: I) -> Result<Self, KvError>
    {
        match self.read_item_and_list(key) {
            Ok((item, list_elements)) =>
                if trim_length > list_elements.len() {
                    Err(KvError::IndexOutOfRange{ upper_bound: list_elements.len() as usize })
                }
                else {
                    let new_list_elements = list_elements.skip(trim_length as int);
                    Ok(Self {
                        m: self.m.insert(key, (new_item, new_list_elements)),
                        ..self
                    })
                },
            Err(e) => Err(e),
        }
    }

    pub open spec fn get_keys(self) -> Set<K>
    {
        self.m.dom()
    }
}

// A `RecoveredKvStore` represents the abstract state of a key/value
// store that will result from recovery from the current state of
// storage. It consists of setup parameters and an `AtomicKvStore`.

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct RecoveredKvStore<K, I, L>
{
    pub ps: SetupParameters,
    pub kv: AtomicKvStore<K, I, L>,
}

impl<K, I, L> RecoveredKvStore<K, I, L>
where
    K: std::fmt::Debug,
    L: LogicalRange,
{
    pub open spec fn init(ps: SetupParameters) -> Self
    {
        Self{ ps, kv: AtomicKvStore::<K, I, L>::init(ps.logical_range_gaps_policy) }
    }
}

// A `KvStoreView` is the abstraction of the state of a running
// key/value store service. Its main fields are `durable`, which
// represents the `AtomicKvStore` that would result from aborting or
// crashing, and `tentative`, which represents the `AtomicKvStore`
// that would result from committing. It also has fields indicating
// how many logical storage slots are used for various purposes, to
// allow for precise specifications of the conditions under which the
// KV store is permitted to fail with an "out of space" error.
//
// Its main operations are `abort`, which sets `tentative` to
// `durable`, and `commit`, which sets `durable` to `tentative`. Both
// reset the number of slots used for keys to the number of keys in
// the store, reset the number of slots used for list elements to the
// number of list elements, and rest the number of slots used for
// transaction operations to zero. Proving we meet these reset
// specifications proves that we don't leak storage space.

#[verifier::reject_recursive_types(K)]
pub struct KvStoreView<K, I, L>
{
    pub ps: SetupParameters,
    pub used_key_slots: int,
    pub used_list_element_slots: int,
    pub used_transaction_operation_slots: int,
    pub pm_constants: PersistentMemoryConstants,
    pub durable: AtomicKvStore<K, I, L>,
    pub tentative: AtomicKvStore<K, I, L>,
    pub powerpm_id: int,
}

impl <K, I, L> KvStoreView<K, I, L>
where
    K: Hash + Eq + std::fmt::Debug,
    L: LogicalRange,
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.ps.logical_range_gaps_policy == self.durable.logical_range_gaps_policy
        &&& self.ps.logical_range_gaps_policy == self.tentative.logical_range_gaps_policy
    }

    pub open spec fn abort(self) -> Self
    {
        Self{
            tentative: self.durable,
            used_key_slots: self.durable.num_keys(),
            used_list_element_slots: self.durable.num_list_elements(),
            used_transaction_operation_slots: 0,
            ..self
        }
    }

    pub open spec fn commit(self) -> Self
    {
        Self{
            durable: self.tentative,
            used_key_slots: self.tentative.num_keys(),
            used_list_element_slots: self.tentative.num_list_elements(),
            used_transaction_operation_slots: 0,
            ..self
        }
    }
}

}
