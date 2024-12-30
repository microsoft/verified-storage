//! This file contains the verified implementation of the KV store. The methods
//! defined here are meant to be called by methods in kvimpl_t.rs with `Perm`
//! arguments that have been audited along with the rest of that file.
//!
//! The UntrustedKvStoreImpl is split into two key components: a volatile index
//! and a durable store. Each of these may be further split into separate components,
//! but having a high-level split between volatile and durable should make the
//! distinction between updates that require crash-consistency proofs, and updates
//! that don't, clear. The view of an UntrustedKvStoreImpl is obtained using the contents
//! of its current volatile and durable components.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::kvimpl_t::*;
use super::kvspec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
pub struct UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    id: u128,
    phantom_pm: core::marker::PhantomData<PM>,
    phantom_k: core::marker::PhantomData<K>,
    phantom_i: core::marker::PhantomData<I>,
    phantom_l: core::marker::PhantomData<L>,
}

pub open spec fn untrusted_recover<K, I, L>(mem: Seq<u8>) -> Option<AbstractKvStoreState<K, I, L>>
{
    None
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
{
    pub closed spec fn pm_constants(self) -> PersistentMemoryConstants
    {
        arbitrary()
    }

    pub closed spec fn view(&self) -> AbstractKvState<K, I, L>
    {
        arbitrary()
    }

    pub closed spec fn valid(self) -> bool
    {
        true
    }

    pub exec fn untrusted_setup(
        pm: &mut PM,
        kvstore_id: u128,
        num_keys: u64, 
        num_list_entries_per_node: u32,
        num_list_nodes: u64,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(pm).inv(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            match result {
                Ok(()) => {
                    &&& pm@.flush_predicted()
                    &&& untrusted_recover::<K, I, L>(pm@.durable_state)
                        == Some(AbstractKvStoreState::<K, I, L>::init(kvstore_id))
                },
                Err(_) => true,
            }
    {
        // 1. flush the pm to ensure there are no outstanding writes
        pm.flush();
        assume(false);
        Ok(())
    }

    pub fn untrusted_start(
        wrpm: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<AbstractKvStoreState<K, I, L>>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<Self, KvError<K>>)
        requires 
            wrpm.inv(),
            wrpm@.flush_predicted(),
            untrusted_recover::<K, I, L>(wrpm@.durable_state) == Some(state),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(state),
        ensures
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv.pm_constants() == wrpm.constants()
                    &&& kv@.valid()
                    &&& kv@.id() == state.id == kvstore_id
                    &&& kv@.durable == state
                    &&& kv@.tentative == state
                }
                Err(KvError::CRCMismatch) => !wrpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.id
                },
                Err(_) => false,
            }
    {        
        assume(false);
        Err(KvError::NotImplemented)
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
                    &&& self@.tentative.read_item(*key) matches Ok(i)
                    &&& item == i
                },
                Err(KvError::KeyNotFound) => !self@.tentative.contains_key(*key),
                Err(e) => {
                    &&& self@.tentative.read_item(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    // This function performs a tentative update to the item of the specified key 
    // as part of an ongoing transaction.
    pub exec fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                },
                Err(e) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Err(e_spec)
                    &&& e_spec == e
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_commit(
        &mut self, 
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable)
                ||| untrusted_recover::<K, I, L>(s) == Some(old(self)@.tentative)
            },
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_delete(
        &mut self,
        key: &K,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> untrusted_recover::<K, I, L>(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self.pm_constants().impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

/*
    // // // TODO: return a Vec<&L> to save space/reduce copies
    // // pub fn untrusted_read_item_and_list(&self, key: &K) -> (result: Option<(&I, Vec<&L>)>)
    // //     requires
    // //         self.valid(),
    // //     ensures
    // //     ({
    // //         let spec_result = self@.read_item_and_list(*key);
    // //         match (result, spec_result) {
    // //             (Some((output_item, output_pages)), Some((spec_item, spec_pages))) => {
    // //                 &&& spec_item == output_item
    // //                 &&& spec_pages == output_pages@
    // //             }
    // //             (Some((output_item, output_pages)), None) => false,
    // //             (None, Some((spec_item, spec_pages))) => false,
    // //             (None, None) => true,
    // //         }
    // //     })
    // // {
    // //     assume(false);
    // //     // First, get the offset of the header in the durable store using the volatile index
    // //     let offset = self.volatile_index.get(key);
    // //     match offset {
    // //         Some(offset) => self.durable_store.read_item_and_list(offset),
    // //         None => None
    // //     }
    // // }

    // pub fn untrusted_read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
    //     requires
    //         self.valid()
    //     ensures
    //         ({
    //             let spec_result = self@.read_list_entry_at_index(*key, idx as int);
    //             match (result, spec_result) {
    //                 (Ok(output_entry), Ok(spec_entry)) => {
    //                     &&& output_entry == spec_entry
    //                 }
    //                 (Err(KvError::IndexOutOfRange), Err(KvError::IndexOutOfRange)) => {
    //                     &&& self@.contents.contains_key(*key)
    //                     &&& self@.contents[*key].1.len() <= idx
    //                 }
    //                 (Err(KvError::KeyNotFound), Err(KvError::KeyNotFound)) => {
    //                     &&& !self@.contents.contains_key(*key)
    //                 }
    //                 (_, _) => false
    //             }
    //         })
    // {
    //     assume(false);
    //     Err(KvError::NotImplemented)
    // }

    // // pub fn untrusted_read_list(&self, key: &K) -> (result: Option<&Vec<L>>)
    // //     requires
    // //         self.valid(),
    // //     ensures
    // //     ({
    // //         let spec_result = self@.read_item_and_list(*key);
    // //         match (result, spec_result) {
    // //             (Some(output_pages), Some((spec_item, spec_pages))) => {
    // //                 &&& spec_pages == output_pages@
    // //             }
    // //             (Some(output_pages), None) => false,
    // //             (None, Some((spec_item, spec_pages))) => false,
    // //             (None, None) => true,
    // //         }
    // //     })
    // // {
    // //     assume(false);
    // //     let offset = self.volatile_index.get(key);
    // //     match offset {
    // //         Some(offset) => self.durable_store.read_list(offset),
    // //         None => None
    // //     }
    // // }

    // pub fn untrusted_delete(
    //     &mut self,
    //     key: &K,
    //     kvstore_id: u128,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.delete(*key).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     // Remove the entry from the volatile index, obtaining the physical offset as the return value
    //     let offset = self.volatile_index.remove(key)?;
    //     self.durable_store.delete(offset, perm)
    // }

    // pub fn untrusted_append_to_list(
    //     &mut self,
    //     key: &K,
    //     new_list_entry: L,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.append_to_list(*key, new_list_entry).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             // TODO: case for if we run out of space to append to the list
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     return Err(KvError::InternalError);
    //     // let offset = self.volatile_index.get(key);
    //     // // append a page to the list rooted at this offset
    //     // let page_offset = match offset {
    //     //     Some(offset) => self.durable_store.append(offset, new_list_entry, perm)?,
    //     //     None => return Err(KvError::KeyNotFound)
    //     // };
    //     // // add the durable location of the page to the in-memory list
    //     // self.volatile_index.append_offset_to_list(key, page_offset)
    // }

    // pub fn untrusted_append_to_list_and_update_item(
    //     &mut self,
    //     key: &K,
    //     new_list_entry: L,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             // TODO: case for if we run out of space to append to the list
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let offset = self.volatile_index.get(key);
    //     // update the header at this offset append a page to the list rooted there
    //     let page_offset = match offset {
    //         Some(offset) => self.durable_store.update_item_and_append(offset, new_list_entry, new_item, perm)?,
    //         None => return Err(KvError::KeyNotFound)
    //     };

    //     // TODO: use append_node_offset or append_to_list depending on whether you need to allocate or not?
    //     self.volatile_index.append_to_list(key)
    // }

    // pub fn untrusted_update_list_entry_at_index(
    //     &mut self,
    //     key: &K,
    //     idx: usize,
    //     new_list_entry: L,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.update_list_entry_at_index(*key, idx, new_list_entry).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     match self.volatile_index.get_entry_location_by_index(key, idx) {
    //         Ok((list_node_addr, offset_within_list_node)) =>
    //             self.durable_store.update_list_entry_at_index(list_node_addr, offset_within_list_node, new_list_entry, perm),
    //         Err(e) => Err(e),
    //     }
    // }

    // pub fn untrusted_update_entry_at_index_and_item(
    //     &mut self,
    //     key: &K,
    //     idx: usize,
    //     new_list_entry: L,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.update_entry_at_index_and_item(*key, idx, new_list_entry, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let header_offset = self.volatile_index.get(key);
    //     match self.volatile_index.get_entry_location_by_index(key, idx) {
    //         Ok((list_node_addr, offset_within_list_node)) =>
    //             self.durable_store.update_entry_at_index_and_item(list_node_addr, offset_within_list_node,
    //                                                               new_item, new_list_entry,  perm),
    //         Err(e) => Err(e),
    //     }
    // }

    // pub fn untrusted_trim_list(
    //     &mut self,
    //     key: &K,
    //     trim_length: usize,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.trim_list(*key, trim_length as int).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    //     {
    //     // use the volatile index to figure out which physical offsets should be removed
    //     // from the list, then use that information to trim the list on the durable side
    //     // TODO: trim_length is in terms of list entries, not bytes, right? Check Jay's impl
    //     // note: we trim from the beginning of the list, not the end
    //     assume(false);
    //     let item_offset = match self.volatile_index.get(key) {
    //         Some(header_addr) => header_addr,
    //         None => return Err(KvError::KeyNotFound),
    //     };
    //     if trim_length == 0 {
    //         return Ok(());
    //     }
    //     let first_location_trimmed = self.volatile_index.get_entry_location_by_index(key, 0);
    //     let last_location_trimmed = self.volatile_index.get_entry_location_by_index(key, trim_length - 1);
    //     self.volatile_index.trim_list(key, trim_length)?;
    //     match (first_location_trimmed, last_location_trimmed) {
    //         (Ok((first_trimmed_list_node_addr, first_trimmed_offset_within_list_node)),
    //          Ok((last_trimmed_list_node_addr, last_trimmed_offset_within_list_node))) =>
    //             // TODO: The interface to `DurableKvStore::trim_list` might
    //             // need to change, to also take
    //             // `first_trimmed_offset_within_list_node` and
    //             // `last_trimmed_offset_within_list_node`.
    //             self.durable_store.trim_list(item_offset, first_trimmed_list_node_addr, last_trimmed_list_node_addr, trim_length, perm),
    //         (Err(e), _) => Err(e),
    //         (_, Err(e)) => Err(e),
    //     }
    // }

    // pub fn untrusted_trim_list_and_update_item(
    //     &mut self,
    //     key: &K,
    //     trim_length: usize,
    //     new_item: I,
    //     perm: Tracked<&TrustedKvPermission>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid()
    //     ensures
    //         match result {
    //             Ok(()) => {
    //                 &&& self.valid()
    //                 &&& self@ == old(self)@.trim_list_and_update_item(*key, trim_length as int, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let item_offset = match self.volatile_index.get(key) {
    //         Some(header_addr) => header_addr,
    //         None => return Err(KvError::KeyNotFound),
    //     };
    //     if trim_length == 0 {
    //         return Ok(());
    //     }
    //     let first_location_trimmed = self.volatile_index.get_entry_location_by_index(key, 0);
    //     let last_location_trimmed = self.volatile_index.get_entry_location_by_index(key, trim_length - 1);
    //     self.volatile_index.trim_list(key, trim_length)?;
    //     match (first_location_trimmed, last_location_trimmed) {
    //         (Ok((first_trimmed_list_node_addr, first_trimmed_offset_within_list_node)),
    //          Ok((last_trimmed_list_node_addr, last_trimmed_offset_within_list_node))) =>
    //             // TODO: The interface to `DurableKvStore::trim_list` might
    //             // need to change, to also take
    //             // `first_trimmed_offset_within_list_node` and
    //             // `last_trimmed_offset_within_list_node`.
    //             self.durable_store.trim_list_and_update_item(item_offset, first_trimmed_list_node_addr, last_trimmed_list_node_addr, trim_length, new_item, perm),
    //         (Err(e), _) => Err(e),
    //         (_, Err(e)) => Err(e),
    //     }
    // }

    // pub fn untrusted_get_keys(&self) -> (result: Vec<K>)
    //     requires
    //         self.valid()
    //     ensures
    //         result@.to_set() == self@.get_keys()
    // {
    //     assume(false);
    //     self.volatile_index.get_keys()
    // }

    */

    // pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
    //     requires
    //         self.valid(),
    //     ensures
    //         match result {
    //             true => self@[*key] is Some,
    //             false => self@[*key] is None
    //         }
    // {
    //     assume(false);
    //     self.volatile_index.get(key).is_some()
    // }

}

}
