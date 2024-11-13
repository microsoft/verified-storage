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
use super::durable::listlayout_v::*;
use super::durable::itemtablelayout_v::*;
use super::kvimpl_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_v::*;
use crate::log2::logimpl_v::*;
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
    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L>
    {
        self.untrusted_kv_impl@
    }

    pub closed spec fn tentative_view(&self) -> AbstractKvStoreState<K, I, L>
    {
        self.untrusted_kv_impl.tentative_view()
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
                    &&& pm_region@.no_outstanding_writes()
                    &&& AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(pm_region@.committed(), kvstore_id) matches Some(recovered_view)
                    &&& recovered_view == AbstractKvStoreState::<K, I, L>::init(kvstore_id)
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
            AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(pm_region@.flush().committed(), kvstore_id) is Some,
            K::spec_size_of() > 0,
            I::spec_size_of() + u64::spec_size_of() <= u64::MAX,
            vstd::std_specs::hash::obeys_key_model::<K>(),
        ensures 
            match result {
                Ok(kvstore) => kvstore.valid(),
                Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                // TODO: proper handling of other error types
                Err(KvError::LogErr { log_err }) => true,
                Err(KvError::InternalError) => true,
                Err(KvError::IndexOutOfRange) => true,
                Err(KvError::PmemErr{ pmem_err }) => true,
                Err(_) => false // TODO
            }
    {
        let mut wrpm_region = WriteRestrictedPersistentMemoryRegion::new(pm_region);
        wrpm_region.flush(); // ensure there are no outstanding writes
        let ghost state = AbstractKvStoreState::<K, I, L>::recover::<TrustedKvPermission::<PM>, PM>(wrpm_region@.committed(), kvstore_id).unwrap();
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(kvstore_id, state);
        let durable_store = UntrustedKvStoreImpl::<PM, K, I, L>::untrusted_start(
            wrpm_region, kvstore_id, Ghost(state), Tracked(&perm))?;

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
                    match self.tentative_view()[*key] {
                        Some(i) => i.0 == item,
                        None => false,
                    }
                }
                Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption,
                Err(KvError::KeyNotFound) => !self.tentative_view().contains_key(*key),
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
                    Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == 
                        old(self).tentative_view().create(*key, *item)
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& !self.constants().impervious_to_corruption
                }, 
                Err(KvError::KeyAlreadyExists) => {
                    &&& self@ == old(self)@
                    &&& old(self).tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    // TODO
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@);
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
                    Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == 
                        old(self).tentative_view().update_item(*key, *item)
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& !self.constants().impervious_to_corruption
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& !self.tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    // TODO
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@);
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
                    Ok::<AbstractKvStoreState<K, I, L>, KvError<K>>(self.tentative_view()) == 
                        old(self).tentative_view().delete(*key)
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& !self.constants().impervious_to_corruption
                }, 
                Err(KvError::KeyNotFound) => {
                    &&& self@ == old(self)@
                    &&& !old(self).tentative_view().contains_key(*key)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    // TODO
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::<PM>::new_one_possibility(self.id, self@);
        self.untrusted_kv_impl.untrusted_delete(key, self.id, Tracked(&perm))
    }

    // TODO @hayley ensure this verifies
    pub exec fn commit(&mut self) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self).tentative_view()
                    &&& self@ == self.tentative_view()
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@
                    &&& !self.constants().impervious_to_corruption
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@
                    // TODO
                }
                Err(KvError::LogErr { log_err }) => {
                    &&& self@ == old(self)@
                    // TODO
                }
                Err(_) => false,
            }
    {
        let tracked perm = TrustedKvPermission::new_two_possibilities(self.id, self@, self.tentative_view());
        self.untrusted_kv_impl.untrusted_commit(self.id, Tracked(&perm))
    }

    /* 
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
    */

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
