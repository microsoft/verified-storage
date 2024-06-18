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
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::itemtable::itemtableimpl_v::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::itemtable::layout_v::*;
use crate::kv::durable::metadata::metadataimpl_v::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::volatile::volatilespec_t::*;
use crate::log::logimpl_v::*;
use crate::log::logimpl_t::*;
use crate::log::logspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use std::hash::Hash;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct DurableKvStore<PM, K, I, L, E>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Item<K> + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug,
        E: std::fmt::Debug,
    {
        item_table: DurableItemTable<K, I, E>,
        durable_list: DurableList<K, L, E>,
        log: UntrustedOpLog<K, L, E>,
        metadata_table: MetadataTable<K, E>,
        item_table_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
        list_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        log_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
        metadata_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>
    }

    impl<PM, K, I, L, E> DurableKvStore<PM, K, I, L, E>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Item<K> + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
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

        // This function doesn't take a perm because it performs initial setup
        // for each structure, which we don't guarantee will be crash consistent
        // TODO: the handling of the PM regions is gross right now, but will get better 
        // with the cleaner subregion approach
        pub fn setup(
            metadata_pmem: &mut PM,
            item_table_pmem: &mut PM,
            list_pmem: &mut PM,
            log_pmem: &mut PM,
            kvstore_id: u128,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K, E>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(metadata_pmem).inv(),
                old(item_table_pmem).inv(),
                old(list_pmem).inv(),
                old(log_pmem).inv(),
                // TODO
            ensures 
               // TODO
        {
            // TODO: where do component IDs come from -- same as kv store? or generate new?

            assume(false);

            // 1. Set up each component in its specified pm region
            MetadataTable::setup(metadata_pmem, kvstore_id, num_keys, L::size_of() as u32, node_size)?;
            DurableItemTable::<K, I, E>::setup(item_table_pmem, kvstore_id, num_keys as u64)?;
            DurableList::<K, L, E>::setup(list_pmem, kvstore_id, num_keys, node_size)?;
            if let Err(e) =  UntrustedLogImpl::setup(log_pmem, kvstore_id) {
                return Err(KvError::LogErr { log_err: e });
            };

            Ok(())
        }

        pub fn start(
            mut metadata_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedMetadataPermission, PM>,
            mut item_table_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedItemTablePermission, PM>,
            mut list_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            mut log_wrpm: WriteRestrictedPersistentMemoryRegion<TrustedPermission, PM>,
            kvstore_id: u128,
            num_keys: u64,
            node_size: u32,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>,
            Ghost(state): Ghost<DurableKvStoreView<K, I, L, E>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                metadata_wrpm.inv(),
                item_table_wrpm.inv(),
                list_wrpm.inv(),
                log_wrpm.inv(),
                L::spec_size_of() + u64::spec_size_of() <= u32::MAX
                // TODO
            ensures
                metadata_wrpm.inv(),
                item_table_wrpm.inv(),
                list_wrpm.inv(),
                log_wrpm.inv(),
                // TODO
        {
            assume(false);

            // TEMPORARY, NOT CORRECT: make up a permissions struct for each component to start with. since we aren't 
            // writing any proofs yet, we don't need the perm to be correct.
            // These perms should actually be derived from the higher-level kv permission
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();

            let list_element_size = (L::size_of() + traits_t::size_of::<u64>()) as u32;

            // 1. Recover the log to get the list of log entries.
            // TODO: we only need to replay the log if we crashed? We don't have clean shutdown implemented right now anyway though
            let mut log: UntrustedOpLog<K, L, E> = UntrustedOpLog::start(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;
            let log_entries = log.read_op_log(&log_wrpm, kvstore_id)?;

            // 2. start the rest of the components using the log

            let metadata_table = MetadataTable::start(&mut metadata_wrpm, kvstore_id, &log_entries, Tracked(&fake_metadata_perm), Ghost(MetadataTableView::init(list_element_size, node_size, num_keys)))?;
            let item_table: DurableItemTable<K, I, E> = DurableItemTable::start(&mut item_table_wrpm, kvstore_id, &log_entries, Tracked(&fake_item_table_perm), Ghost(DurableItemTableView::init(num_keys as int)))?;
            let durable_list = DurableList::start(&mut list_wrpm, kvstore_id, node_size, &log_entries, Tracked(&fake_list_perm), Ghost(DurableListView::init()))?;

            metadata_wrpm.flush();
            item_table_wrpm.flush();
            list_wrpm.flush();
            log_wrpm.flush();

            // 3. we've successfully replayed the log. clear it to free up space for a new transaction
            match log.clear_log(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm)) {
                Ok(()) => {
                    Ok(Self {
                        item_table,
                        durable_list,
                        log,
                        metadata_table,
                        item_table_wrpm,
                        list_wrpm,
                        log_wrpm,
                        metadata_wrpm
                    })
                }
                Err(e) => Err(KvError::LogErr { log_err: e })
            }
        }

        pub fn create(
            &mut self,
            item: &I,
            key: &K,
            Ghost(kvstore_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L, E>>
        ) -> (result: Result<u64, KvError<K, E>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                ({
                    match result {
                        Ok(offset) => {
                            let spec_result = old(self)@.create(offset as int, *item);
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

            // 1. find a free slot in the item table and tentatively write the new item there
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let item_index = self.item_table.tentatively_write_item(
                &mut self.item_table_wrpm, 
                Ghost(kvstore_id), 
                &item, 
                Tracked(&fake_item_table_perm)
            )?;

            // 2. allocate and initialize a head node for this entry; this is tentative since the node is 
            // not yet accessible 
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let head_index = self.durable_list.alloc_and_init_list_node(
                &mut self.list_wrpm, 
                Ghost(kvstore_id), 
                Tracked(&fake_list_perm)
            )?;

            // 3. find a free slot in the metadata table and tentatively write a new entry to it
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let metadata_index = self.metadata_table.tentative_create(
                &mut self.metadata_wrpm, 
                Ghost(kvstore_id), 
                item_index, 
                head_index, 
                key,
                Tracked(&fake_metadata_perm)
            )?;

            // 2. tentatively append the new item's commit op to the log. Metadata entry commit 
            // implies item commit and also makes the list accessible so we can append to it
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            // let log_entry = CommitMetadataEntry::new(metadata_index, item_index);

            // TODO finish this -- write the log entry, commit the transaction, finish off the operation
            // figure out exactly what you need to do here


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
