//! This file contains the public interface of the paged key-value store.
//! The methods offered by this file should match the mocks.
//! The key-value store itself should be as generic as possible, not
//! restricted to particular data structures.
//!
//! TODO: handle errors properly in postconditions

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::durable::durableimpl_v::*;
use super::durable::durablespec_t::*;
use super::pagedkvimpl_v::*;
use super::pagedkvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::pmem::pmemspec_t::*;
use std::hash::Hash;

verus! {

// The page type must satisfy the `LogicalRange` trait, giving it a
// logical range with a `start` and `end`.
pub trait LogicalRange {
    spec fn spec_start(&self) -> int;
    spec fn spec_end(&self) -> int;

    fn start(&self) -> (out: usize)
        ensures
            out == self.spec_start();

    fn end(&self) -> (out: usize)
        ensures
            out == self.spec_end();
}

// Keys, headers, and pages must satisfy the `Serializable` trait so
// that they can be serialized to persistent memory. In particular, it
// must specify a constant maximum size `MAX_BYTES` for such
// serialization.
pub trait Serializable<E>: Sized {
    // const MAX_BYTES: usize;
    fn max_bytes(&self) -> usize; // TODO: verus does not support associated constants

    fn serialize(&self, buffer: &mut [u8]) -> Result<(), E>;
    fn deserialize(buffer: &[u8]) -> Result<Self, E>;
}

#[derive(Debug, PartialEq, Clone)]
pub enum PagedKvError<K, E>
where
    K: std::fmt::Debug,
    E: std::fmt::Debug,
{
    NotImplemented,
    InvalidParameter,
    InternalError, // TODO: reason
    KeyNotFound,
    KeyAlreadyExists,
    InvalidKey{ key: K },
    IndexOutOfRange,
    RegionTooSmall { required: usize, actual: usize },
    OutOfSpace,
    InvalidPersistentMemoryRegionProvided, // TODO: reason
    SerializationError { error: E },
    DeserializationError { error: E },
    LogicalRangeHasBeenTrimmed,
    LogicalRangeHasBeenPartiallyTrimmed,
    LogicalRangePartiallyBeyondEOF,
    LogicalRangeBeyondEOF,
    PageOutOfLogicalRangeOrder,
    PageLeavesLogicalRangeGap,
    LogicalRangeUpdateNotAllowed,
}

pub enum LogicalRangeGapsPolicy {
    LogicalRangeGapsForbidden,
    LogicalRangeGapsPermitted,
}

// TODO: should the constructor take one PM region and break it up into the required sub-regions,
// or should the caller provide it split up in the way that they want?
// TODO: actually should this be a wrapper around an untrusted implementation?
pub struct PagedKv<PM, K, H, P, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
    H: Serializable<E> + std::fmt::Debug,
    P: Serializable<E> + LogicalRange + std::fmt::Debug,
    D: DurableKvStore<PM, K, H, P, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    id: u128,
    untrusted_kv_impl: UntrustedPagedKvImpl<PM, K, H, P, D, V, E>,
}

// TODO: is there a better way to handle PhantomData?
#[verifier::external_body]
pub closed spec fn spec_phantom_data<V: ?Sized>() -> core::marker::PhantomData<V> {
    core::marker::PhantomData::default()
}

impl<PM, K, H, P, D, V, E> PagedKv<PM, K, H, P, D, V, E>
where
    PM: PersistentMemoryRegions,
    K: Hash + Eq + Clone + Serializable<E> + std::fmt::Debug,
    H: Serializable<E> + std::fmt::Debug,
    P: Serializable<E> + LogicalRange + std::fmt::Debug,
    D: DurableKvStore<PM, K, H, P, E>,
    V: VolatileKvIndex<K, E>,
    E: std::fmt::Debug,
{
    pub closed spec fn view(&self) -> AbstractKvStoreState<K, H, P>
    {
        self.untrusted_kv_impl@
    }

    pub closed spec fn valid(self) -> bool
    {
        self.untrusted_kv_impl.valid()
    }

    /// The `PagedKv` constructor calls the constructors for the durable and
    /// volatile components of the key-value store.
    fn new(
        pmem: PM,
        kvstore_id: u128,
        max_keys: usize,
        lower_bound_on_max_pages: usize,
        logical_range_gaps_policy: LogicalRangeGapsPolicy,
    ) -> (result: Result<Self, PagedKvError<K, E>>)
        ensures
            match result {
                Ok(new_kv) => {
                    &&& new_kv.valid()
                }
                Err(_) => true
            }
    {
        Ok(
            Self {
                id: kvstore_id,
                untrusted_kv_impl: UntrustedPagedKvImpl::new(
                    pmem,
                    kvstore_id,
                    max_keys,
                    lower_bound_on_max_pages,
                    logical_range_gaps_policy
                )?
            }
        )
    }

    // TODO: write spec for this operation
    fn restore(pmem: PM, region_size: usize, kvstore_id: u128) -> Result<Self, PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn create(&mut self, key: &K, header: H) -> (result: Result<(), PagedKvError<K, E>>)
        requires
            old(self).valid()
        ensures
            match result {
                Ok(()) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.create(*key, header)
                }
                Err(_) => true
            }
    {
        Err(PagedKvError::NotImplemented)
    }

    fn read_header(&self, key: &K) -> (result: Option<&H>)
        requires
            self.valid()
        ensures
        ({
            let spec_result = self@.read_header_and_pages(*key);
            match (result, spec_result) {
                (Some(output_header), Some((spec_header, pages))) => {
                    &&& spec_header == output_header
                }
                _ => {
                    let spec_result = self@.read_header_and_pages(*key);
                    spec_result.is_None()
                }
            }
        })
    {
        assume(false);
        None
    }

    fn read_header_and_pages(&self, key: &K) -> Option<(&H, &Vec<P>)>
    {
        None
    }

    fn read_pages(&self, key: &K) -> Option<&Vec<P>>
    {
        None
    }

    fn update_header(&mut self, key: &K, new_header: H) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn delete(&mut self, key: &K) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn find_page_with_logical_range_start(&self, key: &K, start: usize) -> Result<Option<usize>, PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn find_pages_in_logical_range(&self, key: &K, start: usize, end: usize) -> Result<Vec<&P>, PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn append_page(&mut self, key: &K, new_index: P) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn append_page_and_update_header(
        &mut self,
        key: &K,
        new_index: P,
        new_header: H,
    ) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn update_page(&mut self, key: &K, idx: usize, new_index: P) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn update_page_and_header(
        &mut self,
        key: &K,
        idx: usize,
        new_index: P,
        new_header: H,
    ) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn trim_pages(
        &mut self,
        key: &K,
        trim_length: usize,
    ) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn trim_pages_and_update_header(
        &mut self,
        key: &K,
        trim_length: usize,
        new_header: H,
    ) -> Result<(), PagedKvError<K, E>>
    {
        Err(PagedKvError::NotImplemented)
    }

    fn get_keys(&self) -> Vec<K>
    {
        Vec::new()
    }
}

}
