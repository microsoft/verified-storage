//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::kv::durable::durablelist::durablelistimpl_v::*;
use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::durable::durablelist::layout_v::*;
use crate::kv::durable::durablespec_t::*;
use crate::kv::durable::itemtable::itemtableimpl_v::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::multilog::multilogimpl_t::*;
use crate::multilog::multilogimpl_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;

use crate::pmem::serialization_t::*;
use std::hash::Hash;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct DurableKvStore<PM, K, I, L, E>
    where
        PM: PersistentMemoryRegions,
        K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
        I: Serializable + Item<K> + Sized + std::fmt::Debug,
        L: Serializable + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        item_table: DurableItemTable<K, I, E>,
        durable_list: DurableList<K, L, E>,
        log: UntrustedMultiLogImpl,
        table_wrpm: WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
        list_wrpm: WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
        log_wrpm: WriteRestrictedPersistentMemoryRegions<TrustedMultiLogPermission, PM>,
    }

    impl<PM, K, I, L, E> DurableKvStore<PM, K, I, L, E>
        where
            PM: PersistentMemoryRegions,
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        // TODO: write this based on specs of the other structures
        pub closed spec fn view(&self) -> DurableKvStoreView<K, I, L, E>;

        // Proving crash consistency here will come down to proving that each update
        // to an individual component results in a valid AbstractKvStoreState either with 0
        // log entries replayed or all of the log entries replayed, I think
        pub closed spec fn recover_to_kv_state(bytes: Seq<Seq<u8>>, id: u128) -> Option<AbstractKvStoreState<K, I, L, E>>
        {
            // TODO
            None
        }

        pub closed spec fn valid(self) -> bool
        {
            // TODO
            true
        }

        // // This function doesn't take a perm because it performs initial setup
        // // for each structure, which we don't guarantee will be crash consistent
        // pub fn setup(
        //     mut pmem: PM,
        //     kvstore_id: u128,
        //     num_keys: u64,
        //     node_size: u32,
        //     // lower_bound_on_max_pages: usize,
        // ) -> (result: Result<(PM, PM, PM), KvError<K, E>>)
        //     requires
        //         pmem.inv(),
        //         ({
        //             let metadata_size = ListEntryMetadata::spec_serialized_len();
        //             let key_size = K::spec_serialized_len();
        //             let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
        //             let list_element_slot_size = L::spec_serialized_len() + CRC_SIZE;
        //             &&& metadata_slot_size <= u64::MAX
        //             &&& list_element_slot_size <= u64::MAX
        //             &&& ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys) <= u64::MAX
        //             &&& ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size <= u64::MAX
        //         }),
        //         L::spec_serialized_len() + CRC_SIZE < u32::MAX, // serialized_len is u64, but we store it in a u32 here
        //         node_size < u32::MAX,
        //         0 <= ItemTableMetadata::spec_serialized_len() + CRC_SIZE < usize::MAX,
        //         ({
        //             let item_slot_size = I::spec_serialized_len() + CDB_SIZE + CRC_SIZE;
        //             &&& 0 <= item_slot_size < usize::MAX
        //             &&& 0 <= item_slot_size * num_keys < usize::MAX
        //             &&& 0 <= ABSOLUTE_POS_OF_TABLE_AREA + (item_slot_size * num_keys) < usize::MAX
        //         })
        //     ensures
        //         match(result) {
        //             Ok((log_region, list_regions, item_region)) => {
        //                 &&& log_region.inv()
        //                 &&& list_regions.inv()
        //                 &&& item_region.inv()
        //             }
        //             Err(_) => true // TODO
        //         }
        // {
        //     // TODO: what ID should we use for the new components? Should we generate a new one
        //     // for each, or should it match the KV store?

        //     // 1. split given PM regions up so that each corresponds with one of the
        //     // durable components
        //     let num_regions = pmem.get_num_regions();
        //     if num_regions < 4 {
        //         return Err(KvError::TooFewRegions {required: 4, actual: num_regions });
        //     } else if num_regions > 4 {
        //         return Err(KvError::TooManyRegions {required: 4, actual: num_regions });
        //     }

        //     let mut log_region = pmem.split_off(3);
        //     let mut list_regions = pmem.split_off(1);
        //     let mut item_table_region = pmem;

        //     // 2. set up each component
        //     // the component setup functions will make sure that the regions are large enough
        //     let result = UntrustedMultiLogImpl::setup(&mut log_region, kvstore_id);
        //     if let Err(e) = result {
        //         return Err(KvError::MultiLogErr { err: e });
        //     }

        //     DurableList::<K, L, E>::setup(&mut list_regions, kvstore_id, num_keys, node_size)?;

        //     DurableItemTable::<K, I, E>::setup(&mut item_table_region, kvstore_id, num_keys as u64)?;

        //     Ok((log_region, list_regions, item_table_region))
        // }

        // pub fn start(
        //     wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedKvPermission<PM, K, I, L, E>, PM>,
        //     kvstore_id: u128,
        //     Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        //     Ghost(state): Ghost<DurableKvStoreView<K, I, L, E>>
        // ) -> (result: Result<Self, KvError<K, E>>)
        //     where
        //         PM: PersistentMemoryRegions
        //     requires
        //         old(wrpm_regions).inv(),
        //         // TODO
        //     ensures
        //         wrpm_regions.inv()
        //         // TODO
        // {
        //     return Err(KvError::NotImplemented);
        // }

        pub fn create(
            &mut self,
            item: I,
            perm: Tracked<&TrustedKvPermission<PM, K, I, L, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                ({
                    match result {
                        Ok(offset) => {
                            let spec_result = old(self)@.create(offset as int, item);
                            match spec_result {
                                Ok(spec_result) => {
                                    &&& self@.len() == old(self)@.len() + 1
                                    &&& self@ == spec_result
                                    &&& 0 <= offset < self@.len()
                                    &&& self@[offset as int].is_Some()
                                }
                                Err(_) => false
                            }
                        }
                        Err(_) => false
                    }
                })
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn read_item(
            &self,
            offset: u64
        ) -> (result: Option<&I>)
            requires
                self.valid(),
            ensures
                match result {
                    Some(item) => {
                        match self@[offset as int] {
                            Some(entry) => entry.item() == item,
                            None => false
                        }
                    }
                    None => self@[offset as int].is_None()
                }
        {
            assume(false);
            None
        }

        pub fn read_list_entry_at_index(
            &self,
            offset: u64,
            idx: u64
        ) -> (result: Result<&L, KvError<K, E>>)
            requires
                self.valid(),
            ensures
                match (result, self@[offset as int]) {
                    (Ok(output_list_entry), Some(spec_entry)) => {
                        let spec_list_entry = spec_entry.list()[idx as int];
                        &&& spec_list_entry is Some
                        &&& spec_list_entry.unwrap() == output_list_entry
                    }
                    (Err(KvError::IndexOutOfRange), _) => {
                        &&& self@[offset as int] is Some
                        &&& self@[offset as int].unwrap().list()[idx as int] is None
                    }
                    (Err(_), Some(spec_entry)) => false,
                    (Ok(output_list_entry), None) => false,
                    (_, _) => false
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn update_item(
            &mut self,
            offset: u64,
            new_item: I,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[offset as int], self@[offset as int]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.key() == old_entry.key()
                                &&& entry.item() == new_item
                                &&& entry.list() == old_entry.list()
                            }
                            (_, _) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[offset as int].is_None(),
                    Err(_) => true // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn delete(
            &mut self,
            offset: u64,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        self@[offset as int].is_None()
                    }
                    Err(_) => true // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn append(
            &mut self,
            offset: u64,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
                // should require that there is enough space in the tail node
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[offset as int];
                        let new_record = self@.contents[offset as int];
                        &&& new_record.list().list == old_record.list().list.push(new_entry)
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn alloc_list_node_and_append(
            &mut self,
            offset: u64,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(node_phys_offset) => {
                        let old_record = old(self)@.contents[offset as int];
                        let new_record = self@.contents[offset as int];
                        &&& new_record.list().list == old_record.list().list.push(new_entry)
                        &&& new_record.list().node_offset_map ==
                                old_record.list().node_offset_map.insert(node_phys_offset as int, old(self)@.len() as int)
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn update_item_and_append(
            &mut self,
            offset: u64,
            new_entry: L,
            new_item: I,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
                // should require that there is enough space in the tail node
            ensures
                self.valid(),
                match result {
                    Ok(phys_offset) => {
                        let old_record = old(self)@.contents[offset as int];
                        let new_record = self@.contents[offset as int];
                        &&& new_record.item() == new_item
                        &&& new_record.list().list == old_record.list().list.push(new_entry)
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn alloc_list_node_update_item_and_append(
            &mut self,
            offset: u64,
            new_entry: L,
            new_item: I,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(phys_offset) => {
                        let old_record = old(self)@.contents[offset as int];
                        let new_record = self@.contents[offset as int];
                        &&& new_record.item() == new_item
                        &&& new_record.list().list == old_record.list().list.push(new_entry)
                        &&& new_record.list().node_offset_map ==
                                old_record.list().node_offset_map.insert(phys_offset as int, old(self)@.len() as int)
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn update_list_entry_at_index(
            &mut self,
            item_offset: u64, // TODO: is this necessary? maybe just as ghost state
            entry_offset: u64,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[item_offset as int];
                        let new_record = self@.contents[item_offset as int];
                        let list_index = new_record.list().node_offset_map[entry_offset as int];
                        &&& list_index == old_record.list().node_offset_map[entry_offset as int]
                        &&& new_record.list()[list_index as int] is Some
                        &&& new_record.list()[list_index as int].unwrap() == new_entry
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn update_entry_at_index_and_item(
            &mut self,
            item_offset: u64,
            entry_offset: u64,
            new_item: I,
            new_entry: L,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[item_offset as int];
                        let new_record = self@.contents[item_offset as int];
                        let list_index = new_record.list().node_offset_map[entry_offset as int];
                        &&& list_index == old_record.list().node_offset_map[entry_offset as int]
                        &&& new_record.list()[list_index as int] is Some
                        &&& new_record.list()[list_index as int].unwrap() == new_entry
                        &&& new_record.item() == new_item
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn trim_list(
            &mut self,
            item_offset: u64,
            old_head_node_offset: u64,
            new_head_node_offset: u64,
            trim_length: usize,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[item_offset as int];
                        let new_record = self@.contents[item_offset as int];
                        &&& new_record.list().list == old_record.list().list.subrange(trim_length as int, old_record.list().len() as int)
                        // offset map entries pointing to trimmed indices should have been removed from the view
                        &&& forall |i: int| 0 <= old_record.list().node_offset_map[i] < trim_length ==> {
                            new_record.list().offset_index(i) is None
                        }
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub fn trim_list_and_update_item(
            &mut self,
            item_offset: u64,
            old_head_node_offset: u64,
            new_head_node_offset: u64,
            trim_length: usize,
            new_item: I,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
        ) -> (result: Result<(), KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[item_offset as int];
                        let new_record = self@.contents[item_offset as int];
                        &&& new_record.item() == new_item
                        &&& new_record.list().list == old_record.list().list.subrange(trim_length as int, old_record.list().len() as int)
                        // offset map entries pointing to trimmed indices should have been removed from the view
                        &&& forall |i: int| 0 <= old_record.list().node_offset_map[i] < trim_length ==>
                                new_record.list().offset_index(i) is None
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);
            Err(KvError::NotImplemented)
        }
    }
}
