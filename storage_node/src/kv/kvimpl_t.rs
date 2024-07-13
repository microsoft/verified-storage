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
//! WriteRestrictedPersistentMemoryRegion backing the structures.
//! This makes the interface to the untrusted component simpler and
//! will make it easier to distinguish between regions owned by
//! different components.
//!
//! This file is unverified and should be tested/audited for correctness.
//!
//! TODO: handle errors properly in postconditions

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::durable::durableimpl_v::*;
use super::durable::durablelist::layout_v::*;
use super::durable::durablespec_t::*;
use super::durable::itemtable::layout_v::*;
use super::kvimpl_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::log::logimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
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
    TooManyRegions { required: usize, actual: usize},
    OutOfSpace,
    InvalidPersistentMemoryRegionProvided, // TODO: reason
    CRCMismatch,
    InvalidItemTableHeader,
    InvalidListMetadata,
    InvalidListRegionMetadata,
    EntryIsValid,
    EntryIsNotValid,
    InvalidLogEntryType,
    LogErr { log_err: LogErr },
    PmemErr { pmem_err: PmemError },
}

// TODO: is there a better way to handle PhantomData?
#[verifier::external_body]
pub closed spec fn spec_phantom_data<V: ?Sized>() -> core::marker::PhantomData<V> {
    core::marker::PhantomData::default()
}

// TODO: should the constructor take one PM region and break it up into the required sub-regions,
// or should the caller provide it split up in the way that they want?
#[verifier::reject_recursive_types(K)]
pub struct KvStore<PM, K, I, L, V>
where
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    V: VolatileKvIndex<K>,
{
    id: u128,
    untrusted_kv_impl: UntrustedKvStoreImpl<PM, K, I, L, V>,
}

impl<PM, K, I, L, V> KvStore<PM, K, I, L, V>
where
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    V: VolatileKvIndex<K>,
{
    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L>
    {
        self.untrusted_kv_impl@
    }

    pub closed spec fn valid(self) -> bool
    {
        self.untrusted_kv_impl.valid()
    }

    /// The `KvStore` constructor calls the constructors for the durable and
    /// volatile components of the key-value store.
    /// `list_node_size` is the number of list entries in each node (not the number
    /// of bytes used by each node)
    pub fn setup(
        metadata_pmem: &mut PM,
        item_table_pmem: &mut PM,
        list_pmem: &mut PM,
        log_pmem: &mut PM,
        kvstore_id: u128,
        num_keys: u64,
        node_size: u32,
    ) -> (result: Result<(), KvError<K>>)
        requires
            // pmem.inv(),
            // ({
            //     let metadata_size = ListEntryMetadata::spec_size_of();
            //     let key_size = K::spec_size_of();
            //     let metadata_slot_size = metadata_size + crate::pmem::traits_t::size_of::<u64>() + key_size + CDB_SIZE;
            //     let list_element_slot_size = L::spec_size_of() + crate::pmem::traits_t::size_of::<u64>();
            //     &&& metadata_slot_size <= u64::MAX
            //     &&& list_element_slot_size <= u64::MAX
            //     &&& ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys) <= u64::MAX
            //     &&& ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size <= u64::MAX
            // }),
            // L::spec_size_of() + crate::pmem::traits_t::size_of::<u64>() < u32::MAX, // size_of is u64, but we store it in a u32 here
            // node_size < u32::MAX,
            // 0 <= ItemTableMetadata::spec_size_of() + crate::pmem::traits_t::size_of::<u64>() < usize::MAX,
            // ({
            //     let item_slot_size = I::spec_size_of() + CDB_SIZE + crate::pmem::traits_t::size_of::<u64>();
            //     &&& 0 <= item_slot_size < usize::MAX
            //     &&& 0 <= item_slot_size * num_keys < usize::MAX
            //     &&& 0 <= ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) < usize::MAX
            // })
        ensures
            // match(result) {
            //     Ok((log_region, list_regions, item_region)) => {
            //         &&& log_region.inv()
            //         &&& list_regions.inv()
            //         &&& item_region.inv()
            //     }
            //     Err(_) => true // TODO
            // }
    {
        UntrustedKvStoreImpl::<PM, K, I, L, V>::untrusted_setup(metadata_pmem, item_table_pmem, list_pmem, log_pmem, kvstore_id, num_keys, node_size)
    }

    pub fn start(
        metadata_pmem: PM,
        item_table_pmem: PM,
        list_pmem: PM,
        log_pmem: PM,
        kvstore_id: u128,
        num_keys: u64,
        node_size: u32,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            // TODO 
        ensures 
            // TODO 
    {
        assume(false);
        let kv = UntrustedKvStoreImpl::<PM, K, I, L, V>::untrusted_start(metadata_pmem, item_table_pmem, list_pmem, log_pmem, kvstore_id, num_keys, node_size)?;
        Ok(Self {
            untrusted_kv_impl: kv,
            id: kvstore_id,
        })
    }

//     // fn restore(pmem: PM, region_size: usize, kvstore_id: u128) -> (result: Result<Self, KvError<K>>)
//     //     requires
//     //         pmem.inv(),
//     //     ensures
//     //         match result {
//     //             Ok(restored_kv) => {
//     //                 let restored_state = UntrustedKvStoreImpl::<PM, K, I, L, V, E>::recover(pmem@.committed(), kvstore_id);
//     //                 match restored_state {
//     //                     Some(restored_state) => restored_kv@ == restored_state,
//     //                     None => false
//     //                 }
//     //             }
//     //             Err(_) => true // TODO
//     //         }
//     // {
//     //     Err(KvError::NotImplemented)
//     // }

    pub fn create(&mut self, key: &K, item: &I, kvstore_id: u128) -> (result: Result<(), KvError<K>>)
        requires
            // old(self).valid(),
        ensures
            // self.valid(),
            // match result {
            //     Ok(()) => {
            //         &&& self@ == old(self)@.create(*key, *item).unwrap()
            //     }
            //     Err(KvError::KeyAlreadyExists) => {
            //         &&& old(self)@.contents.contains_key(*key)
            //         &&& old(self)@ == self@
            //     }
            //     Err(_) => false
            // }
    {
        assume(false);
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            Err(KvError::KeyAlreadyExists)
        } else {
            let tracked perm =
                TrustedKvPermission::new_two_possibilities(self.id, self@, self@.create(*key, *item).unwrap());
            self.untrusted_kv_impl.untrusted_create(key, item, kvstore_id, Tracked(&perm))
        }
    }

    pub fn read_item(&self, key: &K) -> (result: Result<Box<I>, KvError<K>>)
        requires
            // self.valid()
        ensures
        // ({
        //     let spec_result = self@.read_item_and_list(*key);
        //     match (result, spec_result) {
        //         (Some(output_item), Some((spec_item, pages))) => {
        //             &&& spec_item == output_item
        //         }
        //         (Some(output_item), None) => false,
        //         (None, Some((spec_item, pages))) => false,
        //         (None, None) => true,
        //     }
        // })
    {
        assume(false);
        self.untrusted_kv_impl.untrusted_read_item(key)
    }

//     // fn read_item_and_list(&self, key: &K) -> (result: Option<(&I, Vec<&L>)>)
//     //     requires
//     //         self.valid(),
//     //     ensures
//     //     ({
//     //         let spec_result = self@.read_item_and_list(*key);
//     //         match (result, spec_result) {
//     //             (Some((output_item, output_pages)), Some((spec_item, spec_pages))) => {
//     //                 &&& spec_item == output_item
//     //                 &&& spec_pages == output_pages@
//     //             }
//     //             (Some((output_item, output_pages)), None) => false,
//     //             (None, Some((spec_item, spec_pages))) => false,
//     //             (None, None) => true,
//     //         }
//     //     })
//     // {
//     //     self.untrusted_kv_impl.untrusted_read_item_and_list(key)
//     // }

//     fn read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
//         requires
//             self.valid()
//         ensures
//             ({
//                 let spec_result = self@.read_list_entry_at_index(*key, idx as int);
//                 match (result, spec_result) {
//                     (Ok(output_entry), Ok(spec_entry)) => {
//                         &&& output_entry == spec_entry
//                     }
//                     (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => {
//                         &&& self@.contents.contains_key(*key)
//                         &&& self@.contents[*key].1.len() <= idx
//                     }
//                     (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
//                         &&& !self@.contents.contains_key(*key)
//                     }
//                     (_, _) => false
//                 }
//             })
//     {
//         self.untrusted_kv_impl.untrusted_read_list_entry_at_index(key, idx)
//     }

//     // fn read_list(&self, key: &K) -> (result: Option<&Vec<L>>)
//     //     requires
//     //         self.valid(),
//     //     ensures
//     //     ({
//     //         let spec_result = self@.read_item_and_list(*key);
//     //         match (result, spec_result) {
//     //             (Some(output_pages), Some((spec_item, spec_pages))) => {
//     //                 &&& spec_pages == output_pages@
//     //             }
//     //             (Some(output_pages), None) => false,
//     //             (None, Some((spec_item, spec_pages))) => false,
//     //             (None, None) => true,
//     //         }
//     //     })
//     // {
//     //     self.untrusted_kv_impl.untrusted_read_list(key)
//     // }

    pub fn update_item(&mut self, key: &K, new_item: &I, kvstore_id: u128) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.update_item(*key, *new_item).unwrap()
                }
                Err(KvError::KeyNotFound) => {
                    &&& !old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        if self.untrusted_kv_impl.untrusted_contains_key(key) {
            let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_item(*key, *new_item).unwrap());
            self.untrusted_kv_impl.untrusted_update_item(key, new_item, kvstore_id, Tracked(&perm))
        } else {
            Err(KvError::KeyNotFound)
        }

    }

//     fn delete(&mut self, key: &K, kvstore_id: u128,) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             self.valid(),
//             match result {
//                 Ok(()) => {
//                     &&& self@ == old(self)@.delete(*key).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.delete(*key).unwrap());
//             self.untrusted_kv_impl.untrusted_delete(key, kvstore_id, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     // TODO: remove?
//     fn append_to_list(
//         &mut self,
//         key: &K,
//         new_list_entry: L
//     ) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             self.valid(),
//             match result {
//                 Ok(()) => {
//                     &&& self@ == old(self)@.append_to_list(*key, new_list_entry).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 // TODO: case for if we run out of space to append to the list
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.append_to_list(*key, new_list_entry).unwrap());
//             self.untrusted_kv_impl.untrusted_append_to_list(key, new_list_entry, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn append_to_list_and_update_item(
//         &mut self,
//         key: &K,
//         new_list_entry: L,
//         new_item: I,
//     ) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             self.valid(),
//             match result {
//                 Ok(()) => {
//                     &&& self@ == old(self)@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 // TODO: case for if we run out of space to append to the list
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap());
//             self.untrusted_kv_impl.untrusted_append_to_list_and_update_item(key,  new_list_entry, new_item, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn update_list_entry_at_index(&mut self, key: &K, idx: usize, new_list_entry: L) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             self.valid(),
//             match result {
//                 Ok(()) => {
//                     &&& self@ == old(self)@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap());
//             self.untrusted_kv_impl.untrusted_update_list_entry_at_index(key, idx, new_list_entry, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn update_entry_at_index_and_item(
//         &mut self,
//         key: &K,
//         idx: usize,
//         new_list_entry: L,
//         new_item: I,
//     ) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             match result {
//                 Ok(()) => {
//                     &&& self.valid()
//                     &&& self@ == old(self)@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap());
//             self.untrusted_kv_impl.untrusted_update_entry_at_index_and_item(key,  idx, new_list_entry, new_item, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn trim_list(
//         &mut self,
//         key: &K,
//         trim_length: usize,
//     ) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             match result {
//                 Ok(()) => {
//                     &&& self.valid()
//                     &&& self@ == old(self)@.trim_list(*key, trim_length as int).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.trim_list(*key, trim_length as int).unwrap());
//             self.untrusted_kv_impl.untrusted_trim_list(key, trim_length, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn trim_list_and_update_item(
//         &mut self,
//         key: &K,
//         trim_length: usize,
//         new_item: I,
//     ) -> (result: Result<(), KvError<K>>)
//         requires
//             old(self).valid()
//         ensures
//             match result {
//                 Ok(()) => {
//                     &&& self.valid()
//                     &&& self@ == old(self)@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap()
//                 }
//                 Err(KvError::KeyNotFound) => {
//                     &&& !old(self)@.contents.contains_key(*key)
//                     &&& old(self)@ == self@
//                 }
//                 Err(_) => false
//             }
//     {
//         if self.untrusted_kv_impl.untrusted_contains_key(key) {
//             let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap());
//             self.untrusted_kv_impl.untrusted_trim_list_and_update_item(key, trim_length, new_item, Tracked(&perm))
//         } else {
//             Err(KvError::KeyNotFound)
//         }
//     }

//     fn get_keys(&self) -> (result: Vec<K>)
//         requires
//             self.valid()
//         ensures
//             result@.to_set() == self@.get_keys()
//     {
//         self.untrusted_kv_impl.untrusted_get_keys()
//     }
}

}
