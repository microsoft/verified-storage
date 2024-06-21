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

use super::durable::durableimpl_v::*;
use super::durable::durablelist::layout_v::*;
use super::durable::durablespec_t::*;
use super::durable::itemtable::layout_v::*;
use super::durable::metadata::layout_v::*;
use super::inv_v::*;
use super::kvspec_t::*;
use super::volatile::volatileimpl_v::*;
use super::volatile::volatilespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;

use std::hash::Hash;

verus! {

#[verifier::reject_recursive_types(K)]
pub struct UntrustedKvStoreImpl<PM, K, I, L, V>
where
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    V: VolatileKvIndex<K>,
{
    id: u128,
    durable_store: DurableKvStore<PM, K, I, L>,
    volatile_index: V,
    node_size: u32,
    _phantom: Ghost<core::marker::PhantomData<(PM, K, I, L)>>,
}

impl<PM, K, I, L, V> UntrustedKvStoreImpl<PM, K, I, L, V>
where
    PM: PersistentMemoryRegion,
    K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + std::fmt::Debug + Copy,
    V: VolatileKvIndex<K>,
{
    // This function specifies how all durable contents of the KV
    // should be viewed upon recovery as an abstract paged KV state.
    // TODO: write this
    pub closed spec fn recover(mems: Seq<Seq<u8>>, kv_id: u128) -> Option<AbstractKvStoreState<K, I, L>>
    {
        None
    }

    pub closed spec fn view(&self) -> AbstractKvStoreState<K, I, L>
    {
        AbstractKvStoreState {
            id: self.id,
            contents: AbstractKvStoreState::construct_view_contents(
                self.volatile_index@, self.durable_store@),
        }
    }

    // Proves that if the durable store and volatile index comprising a KV are both empty,
    // then the view of the KV is also empty.
    proof fn lemma_empty_kv(self)
        requires
            self.durable_store@.empty(),
            self.volatile_index@.empty(),
        ensures
            self@.empty()
    {
        lemma_empty_map_contains_no_keys(self.volatile_index@.contents);
        assert(Set::new(|k| self.volatile_index@.contains_key(k)) =~= Set::<K>::empty());
    }

    pub closed spec fn valid(self) -> bool
    {
        &&& self.durable_store@.matches_volatile_index(self.volatile_index@)
        &&& self.durable_store.valid()
        &&& self.volatile_index.valid()
    }

    // This only sets up new durable components for a new KV. We will handle
    // the volatile index in `untrusted_start`
    pub fn untrusted_setup(
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
            //     let metadata_slot_size = metadata_size + crate::pmem::traits_t::size_of::<u64>() + key_size + u64::spec_size_of();
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
            //     let item_slot_size = I::spec_size_of() + u64::spec_size_of() + crate::pmem::traits_t::size_of::<u64>();
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
        assume(false);
        DurableKvStore::<PM, K, I, L>::setup(metadata_pmem, item_table_pmem, list_pmem, log_pmem,
             kvstore_id, num_keys, node_size)
    }

    pub fn untrusted_start(
        metadata_region: PM,
        item_table_region: PM,
        list_region: PM,
        log_region: PM,
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
        // First, start the durable component
        let mut log_wrpm = WriteRestrictedPersistentMemoryRegion::new(log_region);
        let mut metadata_wrpm = WriteRestrictedPersistentMemoryRegion::new(metadata_region);
        let mut item_wrpm = WriteRestrictedPersistentMemoryRegion::new(item_table_region);
        let mut list_wrpm = WriteRestrictedPersistentMemoryRegion::new(list_region);
        let tracked fake_kv_permission = TrustedKvPermission::fake_kv_perm();
        let (mut durable, key_index_pairs) = DurableKvStore::start(metadata_wrpm, item_wrpm, list_wrpm, log_wrpm, kvstore_id, num_keys, node_size, Tracked(&fake_kv_permission)).unwrap();

        // Next, start the volatile component. To run YCSB workloads we may need to 
        // add functionality to the durable component for this to work for an 
        // existing KV store
        let mut volatile = V::new(kvstore_id, num_keys as usize, durable.get_elements_per_node())?;

        // TODO: move this into volatile constructor?
        for i in 0..key_index_pairs.len() {
            assume(false);
            // let (key, index) = &key_index_pairs[i]; <- Verus has an issue with this syntax. TODO: report it
            volatile.insert_key(&key_index_pairs[i].0, key_index_pairs[i].1)?;
        }
    
        Ok(Self {
            id: kvstore_id, 
            durable_store: durable,
            volatile_index: volatile,
            node_size,
            _phantom: Ghost(spec_phantom_data()),
        })
    }

    pub fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        kvstore_id: u128,
        perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == old(self)@.create(*key, *item).unwrap()
                }
                Err(KvError::KeyAlreadyExists) => {
                    &&& old(self)@.contents.contains_key(*key)
                    &&& old(self)@ == self@
                }
                Err(_) => false
            }
    {
        assume(false);
        // check whether the key already exists
        if self.volatile_index.get(key).is_some() {
            return Err(KvError::KeyAlreadyExists);
        }

        let ghost old_durable_state = self.durable_store@;
        let ghost old_volatile_state = self.volatile_index@;
        let ghost old_kv_state = self@;

        // `item` stores its own key, so we don't have to pass its key to the durable
        // store separately.
        let (key_offset, list_head) = self.durable_store.tentative_create(&key, &item, kvstore_id, perm)?;
        self.durable_store.commit(kvstore_id, perm)?;
        self.volatile_index.insert_key(key, key_offset)?;

        // proof {
        //     // the volatile index and durable store match after creating the new entry in both
        //     lemma_volatile_matches_durable_after_create(old_durable_state, old_volatile_state, offset as int, *key, *item);
        //     let new_kv_state = old_kv_state.create(*key, *item).unwrap();
        //     // the kv state reflects the new volatile and durable store states
        //     assert(new_kv_state.contents =~= AbstractKvStoreState::construct_view_contents(
        //             self.volatile_index@, self.durable_store@));
        // }

        Ok(())
    }

    pub fn untrusted_read_item(&self, key: &K) -> (result: Result<Box<I>, KvError<K>>)
        requires
            self.valid()
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
        assume(false); // TODO

        // First, get the offset of the header in the durable store using the volatile index
        let offset = self.volatile_index.get(key);
        match offset {
            Some(offset) => self.durable_store.read_item(self.id, offset),
            None => Err(KvError::KeyNotFound) // TODO: get actual error from volatile?
        }
    }

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

    // pub fn untrusted_update_item(
    //     &mut self,
    //     key: &K,
    //     new_item: I,
    //     kvstore_id: u128,
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
    // ) -> (result: Result<(), KvError<K>>)
    //     requires
    //         old(self).valid(),
    //     ensures
    //         self.valid(),
    //         match result {
    //             Ok(()) => {
    //                 &&& self@ == old(self)@.update_item(*key, new_item).unwrap()
    //             }
    //             Err(KvError::KeyNotFound) => {
    //                 &&& !old(self)@.contents.contains_key(*key)
    //                 &&& old(self)@ == self@
    //             }
    //             Err(_) => false
    //         }
    // {
    //     assume(false);
    //     let offset = self.volatile_index.get(key);
    //     match offset {
    //         Some(offset) => self.durable_store.update_item(offset, kvstore_id, new_item),
    //         None => Err(KvError::KeyNotFound)
    //     }
    // }

    // pub fn untrusted_delete(
    //     &mut self,
    //     key: &K,
    //     kvstore_id: u128,
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     self.durable_store.delete(offset, kvstore_id, perm)
    // }

    // pub fn untrusted_append_to_list(
    //     &mut self,
    //     key: &K,
    //     new_list_entry: L,
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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
    //     perm: Tracked<&TrustedKvPermission<PM, K, I, L>>
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

    pub fn untrusted_contains_key(&self, key: &K) -> (result: bool)
        requires
            self.valid(),
        ensures
            match result {
                true => self@[*key] is Some,
                false => self@[*key] is None
            }
    {
        assume(false);
        self.volatile_index.get(key).is_some()
    }

}

}
