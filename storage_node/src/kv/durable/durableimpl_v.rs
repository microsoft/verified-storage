//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::bytes::u64_to_le_bytes;
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
use crate::pmem::crc_t::*;
use std::hash::Hash;

verus! {
    #[verifier::reject_recursive_types(K)]
    pub struct DurableKvStore<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug,
    {
        item_table: DurableItemTable<K, I>,
        durable_list: DurableList<K, L>,
        log: UntrustedOpLog<K, L>,
        metadata_table: MetadataTable<K>,
        wrpm: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission<PM>, PM>,
        pending_updates: Vec<OpLogEntryType<L>>,
    }

    impl<PM, K, I, L> DurableKvStore<PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        // TODO: write this based on specs of the other structures
        pub closed spec fn view(&self) -> DurableKvStoreView<K, I, L>;

        // Proving crash consistency here will come down to proving that each update
        // to an individual component results in a valid AbstractKvStoreState either with 0
        // log entries replayed or all of the log entries replayed, I think
        pub closed spec fn recover_to_kv_state(bytes: Seq<u8>, id: u128) -> Option<AbstractKvStoreState<K, I, L>>
        {
            // TODO
            None
        }

        pub closed spec fn valid(self) -> bool
        {
            // TODO
            true
        }

        pub exec fn get_elements_per_node(&self) -> u64 {
            self.durable_list.get_elements_per_node()
        }

/*

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
        ) -> (result: Result<(), KvError<K>>)
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
            DurableItemTable::<K, I>::setup(item_table_pmem, kvstore_id, num_keys as u64)?;
            DurableList::<K, L>::setup(list_pmem, kvstore_id, num_keys, node_size)?;
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
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
            // Ghost(state): Ghost<DurableKvStoreView<K, I, L>>
        ) -> (result: Result<(Self, Vec<(Box<K>, u64)>), KvError<K>>)
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
            let mut log: UntrustedOpLog<K, L> = UntrustedOpLog::start(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;
            let log_entries = log.read_op_log(&log_wrpm, kvstore_id)?;
            // 2. start the rest of the components using the log
            let (metadata_table, key_index_pairs) = MetadataTable::start(&mut metadata_wrpm, kvstore_id, &log_entries, Tracked(&fake_metadata_perm), Ghost(MetadataTableView::init(list_element_size, node_size, num_keys)))?;
            let item_table: DurableItemTable<K, I> = DurableItemTable::start(&mut item_table_wrpm, kvstore_id, &log_entries, Tracked(&fake_item_table_perm), Ghost(DurableItemTableView::init(num_keys as int)))?;
            let durable_list = DurableList::start(&mut list_wrpm, kvstore_id, node_size, &log_entries, Tracked(&fake_list_perm), Ghost(DurableListView::init()))?;

            metadata_wrpm.flush();
            item_table_wrpm.flush();
            list_wrpm.flush();
            log_wrpm.flush();

            // 3. we've successfully replayed the log. clear it to free up space for a new transaction
            log.clear_log(&mut log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;
            Ok((
                Self {
                    item_table,
                    durable_list,
                    log,
                    metadata_table,
                    item_table_wrpm,
                    list_wrpm,
                    log_wrpm,
                    metadata_wrpm,
                    pending_updates: Vec::new(),
                }, 
                key_index_pairs
            ))
        }

        // Commits all pending updates by committing the log and applying updates to 
        // each durable component.
        pub fn commit(
            &mut self,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>
        ) -> (result: Result<(), KvError<K>>)
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            // 1. Commit the log
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.commit_log(&mut self.log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;

            // 2. Play the log on each durable component
            let tracked fake_metadata_perm = TrustedMetadataPermission::fake_metadata_perm();
            let tracked fake_item_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            // TODO: handle the ghost states properly here
            self.metadata_table.play_metadata_log(&mut self.metadata_wrpm, kvstore_id, 
                &self.pending_updates, Tracked(&fake_metadata_perm), Ghost(self.metadata_table@))?;
            self.item_table.play_item_log(&mut self.item_table_wrpm, kvstore_id, 
                &self.pending_updates, Tracked(&fake_item_perm), Ghost(self.item_table@))?;
            self.durable_list.play_log_list(&mut self.list_wrpm, kvstore_id, &self.pending_updates, 
                Tracked(&fake_list_perm), Ghost(self.durable_list@))?;

            // 3. Clear the log
            self.log.clear_log(&mut self.log_wrpm, kvstore_id, Tracked(&fake_log_perm))?;

            // 4. Clear the local pending log updates list
            self.pending_updates.clear();

            Ok(())
        }

        // Creates a new durable record in the KV store. Note that since the durable KV store 
        // identifies records by their metadata table index, rather than their key, this 
        // function does NOT return an error if you attempt to create two records with the same 
        // key. Returns the metadata index and the location of the list head node.
        // TODO: Should require caller to prove that the key doesn't already exist in order to create it.
        // The caller should do this because this can be done quickly with the volatile info.
        pub fn tentative_create(
            &mut self,
            key: &K,
            item: &I,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>
        ) -> (result: Result<(u64, u64), KvError<K>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                ({
                    match result {
                        Ok((offset, head_node)) => {
                            let spec_result = old(self)@.create(offset as int, *key, *item);
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
                head_index, 
                item_index, 
                key,
                Tracked(&fake_metadata_perm)
            )?;

            // 4. tentatively append the new item's commit op to the log. Metadata entry commit 
            // implies item commit and also makes the list accessible so we can append to it
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_metadata_table_perm = TrustedMetadataPermission::fake_metadata_perm();

            let item_log_entry: OpLogEntryType<L> = OpLogEntryType::ItemTableEntryCommit { item_index };
            let metadata_log_entry: OpLogEntryType<L> = OpLogEntryType::CommitMetadataEntry { metadata_index };

            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &item_log_entry, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_log_entry, Tracked(&fake_log_perm))?;

            // 5. Add log entries to pending list
            self.pending_updates.push(item_log_entry);
            self.pending_updates.push(metadata_log_entry);

            // 6. Return the index of the metadata entry so it can be used in the volatile index.
            Ok((metadata_index, head_index))
        }

        // This function takes an offset into the METADATA table, looks up the corresponding item,
        // and returns it if it exists.
        pub fn read_item(
            &self,
            kvstore_id: u128,
            metadata_index: u64
        ) -> (result: Result<Box<I>, KvError<K>>)
            requires
                self.valid(),
            ensures
                match result {
                    Ok(item) => {
                        match self@[metadata_index as int] {
                            Some(entry) => entry.item() == item,
                            None => false
                        }
                    }
                    Err(_) => self@[metadata_index as int].is_None()
                }
        {
            assume(false);
            let (key, metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            let item_index = metadata.item_index;
            self.item_table.read_item(self.item_table_wrpm.get_pm_region_ref(), kvstore_id, item_index)
        }

        pub fn get_list_len(
            &self,
            kvstore_id: u128,
            metadata_index: u64
        ) -> Result<u64, KvError<K>>
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            let (_, metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            Ok(metadata.length)
        }

        // TODO: should this require a check to make sure we are reading 
        // from a valid list node and from the key that we expect?
        pub fn read_list_entry_at_index(
            &self,
            node_location: u64,
            index_in_node: u64,
            kvstore_id: u128,
        ) -> (result: Result<Box<L>, KvError<K>>)
            requires
                self.valid(),
            ensures
                match (result, self@[node_location as int]) {
                    (Ok(output_list_entry), Some(spec_entry)) => {
                        let spec_list_entry = spec_entry.list()[index_in_node as int];
                        &&& spec_list_entry is Some
                        &&& spec_list_entry.unwrap() == output_list_entry
                    }
                    (Err(KvError::IndexOutOfRange), _) => {
                        &&& self@[node_location as int] is Some
                        &&& self@[node_location as int].unwrap().list()[index_in_node as int] is None
                    }
                    (Err(_), Some(spec_entry)) => false,
                    (Ok(output_list_entry), None) => false,
                    (_, _) => false
                }
        {
            assume(false);
            self.durable_list.read_element_at_index(self.list_wrpm.get_pm_region_ref(), kvstore_id, node_location, index_in_node)
        }

        pub fn tentative_update_item(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            new_item: &I,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        match (old(self)@[metadata_index as int], self@[metadata_index as int]) {
                            (Some(old_entry), Some(entry)) => {
                                &&& entry.key() == old_entry.key()
                                &&& entry.item() == new_item
                                &&& entry.list() == old_entry.list()
                            }
                            (_, _) => false
                        }
                    }
                    Err(KvError::KeyNotFound) => self@[metadata_index as int].is_None(),
                    Err(_) => true // TODO
                }
        {
            assume(false);
            // 1. Look up current index of the item via the metadata table
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            let old_item_index = metadata.item_index;

            // 2. Tentatively allocate a new item slot and write the new item to it
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let new_item_index = self.item_table.tentatively_write_item(
                &mut self.item_table_wrpm, 
                Ghost(kvstore_id), 
                &new_item, 
                Tracked(&fake_item_table_perm)
            )?;

            // 3. Update the metadata structure with the new item index
            metadata.item_index = new_item_index;

            // 4. Calculate the CRC for the updated metadata together with the key. We cannot 
            // trust that the CRC, key, or metadata are correct during replay in general, so we 
            // either need to log the new CRC or the key so that we can make sure to update the 
            // entry with the correct CRC when we apply the update at commit time. 

            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 5. Log the metadata update, the new item commit, and the old item invalidate
            let metadata_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_metadata: *metadata, new_crc };
            let new_item_commit = OpLogEntryType::ItemTableEntryCommit { item_index: new_item_index };
            let old_item_invalid = OpLogEntryType::ItemTableEntryInvalidate { item_index: old_item_index };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_update, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &new_item_commit, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &old_item_invalid, Tracked(&fake_log_perm))?;

            // 6. Add pending log entries to list
            self.pending_updates.push(metadata_update);
            self.pending_updates.push(new_item_commit);
            self.pending_updates.push(old_item_invalid);

            Ok(())
        }

        pub fn tentative_delete(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid()
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        self@[metadata_index as int].is_None()
                    }
                    Err(_) => true // TODO
                }
        {
            assume(false);

            // TODO: could get rid of item valid/invalid IF we had another way to determine 
            // if they are allocated (like getting that info from the metadata table)

            // TODO: DEALLOCATE LIST NODES

            // 1. look up the item index so that we can invalidate it 
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            let item_index = metadata.item_index;

            // 2. Log the item and metadata invalidation
            let item_invalidate = OpLogEntryType::ItemTableEntryInvalidate { item_index };
            let metadata_invalidate = OpLogEntryType::InvalidateMetadataEntry { metadata_index };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &item_invalidate, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_invalidate, Tracked(&fake_log_perm))?;

            // 3. Add pending log entries to list
            self.pending_updates.push(item_invalidate);
            self.pending_updates.push(metadata_invalidate);

            Ok(())
        }

        // This function appends a new list entry *without* allocating a new list node.
        // It fails if there is no space left in the tail node.
        // TODO: write a variant of this that allows atomically appending an arbitrary number 
        // of list elements (potentially with allocation) in a single transaction
        pub fn tentative_append(
            &mut self,
            metadata_index: u64,
            new_entry: &L,
            node_location: u64, 
            index_in_node: u64, 
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                // should require that there is enough space in the tail node
                // and that the given node is in fact the tail
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[metadata_index as int];
                        let new_record = self@.contents[metadata_index as int];
                        &&& new_record.list().list == old_record.list().list.push(*new_entry)
                    }
                    Err(_) => false // TODO
                }
        {   
            // TODO: add error handling or use preconditions that prevent errors

            assume(false);
            // 1. look up list metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;
            
            // 2. append the new list element to the list. This is a tentative write and does not need to be logged.
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            self.durable_list.append_element(&mut self.list_wrpm, kvstore_id, node_location, 
                index_in_node, &new_entry, Tracked(&fake_list_perm))?;

            // 3. Calculate the new CRC
            metadata.length = metadata.length + 1;
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Log the length update to the metadata
            let list_len_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &list_len_update, Tracked(&fake_log_perm))?;

            // 5. Add pending log entry to list
            self.pending_updates.push(list_len_update);

            Ok(())
        }

        pub fn tentative_alloc_list_node(
            &mut self,
            metadata_index: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<u64, KvError<K>>)
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            // 1. Look up metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            // 2. Tentatively allocate and initialize an unused list node
            let tracked fake_list_perm = TrustedListPermission::fake_list_perm();
            let new_list_node_loc = self.durable_list.alloc_and_init_list_node(&mut self.list_wrpm, Ghost(kvstore_id), Tracked(&fake_list_perm))?;

            // 3. Update the metadata with the new tail node and calculate the new crc
            let old_tail = metadata.tail;
            metadata.tail = new_list_node_loc;
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Log metadata update and list node append 
            let tail_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let node_append = OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail: new_list_node_loc };

            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &tail_update, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &node_append, Tracked(&fake_log_perm))?;

            // 5. Add pending log entries to list
            self.pending_updates.push(tail_update);
            self.pending_updates.push(node_append);

            Ok(new_list_node_loc)
        }

        pub fn tentative_update_list_entry_at_index(
            &mut self,
            node_offset: u64,
            index_in_node: u64,
            new_entry: L,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
            ensures
                self.valid(),
                // TODO
                // match result {
                //     Ok(()) => {
                //         let old_record = old(self)@.contents[item_offset as int];
                //         let new_record = self@.contents[item_offset as int];
                //         let list_index = new_record.list().node_offset_map[entry_offset as int];
                //         &&& list_index == old_record.list().node_offset_map[entry_offset as int]
                //         &&& new_record.list()[list_index as int] is Some
                //         &&& new_record.list()[list_index as int].unwrap() == new_entry
                //     }
                //     Err(_) => false // TODO
                // }
        {
            assume(false);
            
            // Log entry update involves writing to a live list element, so the actual updates are handled by playing the log forward.
            // This operation just creates the log entry and puts it in the tentative transaction
            
            // 1. Create the log entry
            let log_entry = OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element: new_entry };

            // 2. Append the log entry to the log
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &log_entry, Tracked(&fake_log_perm))?;

            // 3. Add the pending log entry to the list
            self.pending_updates.push(log_entry);

            Ok(())
        }

        pub fn tentative_trim_list(
            &mut self,
            metadata_index: u64,
            old_head: u64,
            new_head: u64,
            new_skip: u64, // TODO: who is in charge of figuring this out?
            trim_len: u64,
            kvstore_id: u128,
            Tracked(perm): Tracked<&TrustedKvPermission<PM, K, I, L>>,
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                // TODO: caller needs to prove that the provided head will actually be the head
                // when trimming `trim_len` entries
            ensures
                self.valid(),
                match result {
                    Ok(()) => {
                        let old_record = old(self)@.contents[metadata_index as int];
                        let new_record = self@.contents[metadata_index as int];
                        &&& new_record.list().list == old_record.list().list.subrange(trim_len as int, old_record.list().len() as int)
                        // offset map entries pointing to trimmed indices should have been removed from the view
                        &&& forall |i: int| 0 <= old_record.list().node_offset_map[i] < trim_len ==> {
                            new_record.list().offset_index(i) is None
                        }
                    }
                    Err(_) => false // TODO
                }
        {
            assume(false);

            // 1. Look up list metadata
            let (key, mut metadata) = self.metadata_table.get_key_and_metadata_entry_at_index(
                self.metadata_wrpm.get_pm_region_ref(), kvstore_id, metadata_index)?;

            if trim_len > metadata.length {
                return Err(KvError::IndexOutOfRange);
            }

            // 2. Update the metadata structure 
            metadata.head = new_head;
            metadata.length = metadata.length - trim_len;
            metadata.first_entry_offset = new_skip;
            
            // 3. Calculate the new CRC 
            let mut digest = CrcDigest::new();
            digest.write(&*metadata);
            digest.write(&*key);
            let new_crc = digest.sum64();

            // 4. Append the update to the log 
            let metadata_update = OpLogEntryType::UpdateMetadataEntry { metadata_index, new_crc, new_metadata: *metadata };
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_update, Tracked(&fake_log_perm))?;

            // 5. Add the pending log entry to the list
            self.pending_updates.push(metadata_update);

            // We don't deallocate any nodes here, since nodes that will be trimmed off are in use until we commit
            // the transaction.
            // We'll use a special in-memory-only log entry enum variant to record the old and new heads and 
            // deallocate everything between them during log replay in commit. We don't log this information,
            // but that's ok, because after crash/restart we will replay the log and then rebuild the allocators,
            // which is equivalent to deallocating from the in-memory entry
            let node_dealloc = OpLogEntryType::NodeDeallocInMemory { old_head, new_head };
            self.pending_updates.push(node_dealloc);

            Ok(())
        }
        */
    }
        
}
