//! This file contains the public interface of the paged key-value store.
//! The methods offered by this file should match the mocks.
//! The key-value store itself should be as generic as possible, not
//! restricted to particular data structures.
//! We define legal crash states at this level and pass them
//! to the untrusted implementation, which passes them along
//! to untrusted components.
//!
//! Note that the design of this component is different from the original
//! verified log in that the untrusted implementation, rather than
//! the trusted implementation in this file, owns the
//! PoWERPersistentMemoryRegion backing the structures.
//! This makes the interface to the untrusted component simpler and
//! will make it easier to distinguish between regions owned by
//! different components.
//!
//! This file is unverified and should be tested/audited for correctness.

#![allow(unused_imports)]
#![cfg_attr(verus_keep_ghost, verus::trusted)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::durable::durableimpl_v::*;
use super::durable::listlayout_v::*;
use super::durable::itemtablelayout_v::*;
use super::kvimpl_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_v::*;
use crate::log2::logimpl_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
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
    LogErr { log_err: LogErr },
    PmemErr { pmem_err: PmemError },
}

// TODO: is there a better way to handle PhantomData?
#[verifier::external_body]
pub closed spec fn spec_phantom_data<V: ?Sized>() -> core::marker::PhantomData<V> {
    core::marker::PhantomData::default()
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct KvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    id: u128,
    untrusted_kv_impl: UntrustedKvStoreImpl<PM, K, I, L>,
    // TODO: use generic Perm?
}

impl<PM, K, I, L> KvStore<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    pub closed spec fn view(&self) -> AbstractKvState<K, I, L>
    {
        AbstractKvState::<K, I, L>{
            durable: self.untrusted_kv_impl@,
            tentative: self.untrusted_kv_impl.tentative_view(),
        }
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.untrusted_kv_impl.valid()
        &&& self.id == self.untrusted_kv_impl@.id
    }

    pub closed spec fn constants(self) -> PersistentMemoryConstants
    {
        self.untrusted_kv_impl.constants()
    }

    pub closed spec fn spec_num_log_entries_in_current_transaction(self) -> nat 
    {
        self.untrusted_kv_impl.spec_num_log_entries_in_current_transaction()
    }

    pub exec fn setup(
        pm_region: &mut PM,
        kvstore_id: u128,
        num_keys: u64, 
        num_list_entries_per_node: u32,
        num_list_nodes: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(pm_region).inv(),
        ensures
            pm_region.inv(),
            match result {
                Ok(()) => {
                    &&& pm_region@.flush_predicted()
                    &&& AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(
                        pm_region@.durable_state, kvstore_id) == Some(AbstractKvStoreState::<K, I, L>::init(kvstore_id))
                }
                Err(_) => true
            }
    {
        UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_setup(pm_region, kvstore_id,
            num_keys, num_list_entries_per_node, num_list_nodes)?;
        Ok(())
    }

    pub exec fn start(
        mut pm_region: PM,
        kvstore_id: u128,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            pm_region.inv(),
            AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(pm_region@.read_state, kvstore_id) is Some,
            K::spec_size_of() > 0,
            I::spec_size_of() + u64::spec_size_of() <= u64::MAX,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures 
            match result {
                Ok(kvstore) => kvstore.valid(),
                Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption(),
                Err(_) => false,
            }
    {
        let mut powerpm_region = PoWERPersistentMemoryRegion::new(pm_region);
        powerpm_region.flush(); // ensure there are no outstanding writes
        let ghost state = AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(powerpm_region@.durable_state, kvstore_id).unwrap();
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(kvstore_id, state);
        let durable_store = UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_start(
            powerpm_region, kvstore_id, Ghost(state), Tracked(&perm))?;

        Ok(Self {
            id: kvstore_id,
            untrusted_kv_impl: durable_store
        })
    }

    pub exec fn read_item(
        &self,
        key: &K,
    ) -> (result: Result<Box<I>, KvError<K>>)
        requires 
            self.valid(),
        ensures 
            match result {
                Ok(item) => {
                    match self@.tentative[*key] {
                        Some(i) => i.0 == item,
                        None => false,
                    }
                }
                Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption(),
                Err(KvError::KeyNotFound) => !self@.tentative.contains_key(*key),
                Err(_) => false,
            }
    {
        self.untrusted_kv_impl.read_item(key)
    }

    pub exec fn create(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self@.tentative) == 
                        old(self)@.tentative.create(*key, *item)
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyAlreadyExists) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@.durable);
        let result = self.untrusted_kv_impl.untrusted_create(key, item, self.id, Tracked(&perm));
        result
    }

    pub exec fn update_item(
        &mut self,
        key: &K,
        item: &I,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self@.tentative) == 
                        old(self)@.tentative.update_item(*key, *item)
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& !self@.tentative.contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@.durable);
        self.untrusted_kv_impl.untrusted_update_item(key, item, self.id, Tracked(&perm))
    }

    pub exec fn delete(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self@.tentative) == 
                        old(self)@.tentative.delete(*key)
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& !old(self)@.tentative.contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@.durable);
        self.untrusted_kv_impl.untrusted_delete(key, self.id, Tracked(&perm))
    }

    pub exec fn commit(&mut self) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.commit()
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                }
                Err(KvError::LogErr { log_err }) => {
                    &&& self@ == old(self)@.abort()
                }
                Err(KvError::NoCurrentTransaction) => {
                    &&& self@ == old(self)@
                    &&& self.spec_num_log_entries_in_current_transaction() == 0
                }
                Err(_) => false,
            }
    {
        if self.untrusted_kv_impl.num_log_entries_in_current_transaction() == 0 {
            return Err(KvError::NoCurrentTransaction)
        }
        let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@.durable, self@.tentative);
        self.untrusted_kv_impl.untrusted_commit(self.id, Tracked(&perm))
    }
}

}
