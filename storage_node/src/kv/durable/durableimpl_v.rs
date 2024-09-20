//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::assert_seqs_equal;
use vstd::bytes::u64_from_le_bytes;
use vstd::bytes::u64_to_le_bytes;
use vstd::prelude::*;

use crate::kv::durable::commonlayout_v::*;
use crate::kv::durable::list_v::*;
use crate::kv::durable::listlayout_v::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::itemtable_v::*;
use crate::kv::durable::itemtablelayout_v::*;
use crate::kv::durable::maintable_v::*;
use crate::kv::durable::maintablelayout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::util_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::kvspec_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::kv::volatile::volatilespec_v::*;
use crate::log2::layout_v::*;
use crate::log2::logimpl_v::*;
use crate::log2::inv_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::lemma_establish_extract_bytes_equivalence;
use crate::pmem::wrpm_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use crate::util_v::*;
use std::borrow::Borrow;
use std::hash::Hash;

use super::inv_v::lemma_safe_recovery_writes;

verus! {
    pub struct DurableKvStoreList<L>
    {
        pub list: Seq<L>,
        // pub node_offset_map: Map<int, int> // maps nodes to the first logical list index they contain
    }

    impl<L> DurableKvStoreList<L>
    {
        pub open spec fn spec_index(self, idx: int) -> Option<L>
        {
            if idx < self.list.len() {
                Some(self.list[idx])
            } else {
                None
            }
        }

        // pub open spec fn offset_index(self, offset: int) -> Option<int>
        // {
        //     if self.node_offset_map.contains_key(offset) {
        //         Some(self.node_offset_map[offset])
        //     } else {
        //         None
        //     }
        // }

        pub open spec fn len(self) -> int
        {
            self.list.len() as int
        }

        pub open spec fn empty() -> Self
        {
            DurableKvStoreList {
                list: Seq::empty(),
                // node_offset_map: Map::empty(),
            }
        }
    }

    pub struct DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub key: K,
        pub item: I,
        pub list: DurableKvStoreList<L>,

    }

    // TODO: remove since the fields are public
    impl<K, I, L> DurableKvStoreViewEntry<K, I, L>
    where
        K: Hash + Eq,
    {
        pub open spec fn key(self) -> K
        {
            self.key
        }

        pub open spec fn item(self) -> I
        {
            self.item
        }

        pub open spec fn list(self) -> DurableKvStoreList<L>
        {
            self.list
        }
    }

    pub struct DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub contents: Map<int, DurableKvStoreViewEntry<K, I, L>>,
    }

    impl<K, I, L> DurableKvStoreView<K, I, L>
    where
        K: Hash + Eq + std::fmt::Debug,
    {
        pub open spec fn spec_index(self, idx: int) -> Option<DurableKvStoreViewEntry<K, I, L>>
        {
            if self.contents.contains_key(idx) {
                Some(self.contents[idx])
            } else {
                None
            }
        }

        pub open spec fn init() -> Self {
            Self {
                contents: Map::empty()
            }
        }

        pub open spec fn contains_key(self, idx: int) -> bool
        {
            self[idx] is Some
        }

        pub open spec fn empty(self) -> bool
        {
            self.contents.is_empty()
        }

        pub open spec fn len(self) -> nat
        {
            self.contents.len()
        }

        pub open spec fn create(self, offset: int, key: K, item: I) -> Result<Self, KvError<K>>
        {
            if self.contents.contains_key(offset) {
                Err(KvError::KeyAlreadyExists)
            } else {
                Ok(
                    Self {
                        contents: self.contents.insert(
                            offset,
                            DurableKvStoreViewEntry {
                                key,
                                item,
                                list: DurableKvStoreList::empty()
                            }
                        ),
                    }
                )
            }
        }

        pub open spec fn delete(self, offset: int) -> Result<Self, KvError<K>>
        {
            if !self.contents.contains_key(offset) {
                Err(KvError::KeyNotFound)
            } else {
                Ok(
                    Self {
                        contents: self.contents.remove(offset)
                    }
                )
            }
        }

        pub open spec fn update_item(self, offset: int, item: I) -> Result<Self, KvError<K>>
        {
            if !self.contents.contains_key(offset) {
                Err(KvError::KeyNotFound)
            } else {
                Ok(
                    Self {
                        contents: self.contents.insert(
                            offset,
                            DurableKvStoreViewEntry {
                                key: self.contents[offset].key,
                                item,
                                list: self.contents[offset].list
                            }
                        )
                    }
                )
            }
        }

        pub open spec fn valid(self) -> bool
        {
            true
        }

        // TODO: might be cleaner to define this elsewhere (like in the interface)
        pub open spec fn matches_volatile_index(&self, volatile_index: VolatileKvIndexView<K>) -> bool
        {
            &&& self.len() == volatile_index.contents.len()
            &&& self.contents.dom().finite()
            &&& volatile_index.contents.dom().finite()
            &&& self.valid()
            // all keys in the volatile index are stored at the indexed offset in the durable store
            &&& forall |k: K| #[trigger] volatile_index.contains_key(k) ==> {
                    let indexed_offset = volatile_index[k].unwrap().header_addr;
                    &&& self.contains_key(indexed_offset)
                    &&& self[indexed_offset].unwrap().key == k
                }
            // all offsets in the durable store have a corresponding entry in the volatile index
            &&& forall |i: int| #[trigger] self.contains_key(i) ==> {
                &&& volatile_index.contains_key(self[i].unwrap().key)
                &&& volatile_index[self[i].unwrap().key].unwrap().header_addr == i
            }
        }
    }

    #[verifier::reject_recursive_types(K)]
    pub struct DurableKvStore<Perm, PM, K, I, L>
    where
        Perm: CheckPermission<Seq<u8>>,
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug,
    {
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
        item_table: DurableItemTable<K, I>,
        durable_list: DurableList<K, L>,
        log: UntrustedOpLog<K, L>,
        main_table: MainTable<K>,
        wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
        pending_updates: Vec<PhysicalOpLogEntry>,
    }

    impl<Perm, PM, K, I, L> DurableKvStore<Perm, PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        pub closed spec fn view(&self) -> DurableKvStoreView<K, I, L>
        {
            Self::recover_from_component_views(self.main_table@, self.item_table@, self.durable_list@)
        }

        pub closed spec fn tentative_view(self) -> Option<DurableKvStoreView<K, I, L>>
        {
            Self::physical_recover_after_committing_log(self.wrpm@.flush().committed(), self.overall_metadata, self.log@)
        }

        pub closed spec fn pending_allocations(self) -> Set<u64>
        {
            self.main_table.pending_allocations_view()
        }

        pub closed spec fn pending_deallocations(self) -> Set<u64>
        {
            self.main_table.pending_deallocations_view()
        }

        pub closed spec fn constants(self) -> PersistentMemoryConstants
        {
            self.wrpm.constants()
        }

        pub closed spec fn inv_mem(self, mem: Seq<u8>) -> bool
        {
            &&& self.version_metadata == deserialize_version_metadata(mem)
            &&& self.overall_metadata == deserialize_overall_metadata(mem, self.version_metadata.overall_metadata_addr)
            &&& Self::physical_recover(mem, self.version_metadata, self.overall_metadata) == Some(self@)
        }

        pub closed spec fn inv(self) -> bool 
        {
            let pm_view = self.wrpm@;
            &&& self.wrpm.inv()
            &&& overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr,
                                                self.overall_metadata.kvstore_id)
            &&& self.wrpm@.len() == self.overall_metadata.region_size
            &&& self.log.inv(pm_view, self.version_metadata, self.overall_metadata)
            &&& no_outstanding_writes_to_version_metadata(self.wrpm@)
            &&& no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int)
            &&& forall|s| #[trigger] pm_view.can_crash_as(s) ==> self.inv_mem(s)
            &&& self.main_table.inv(get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat),
                                      self.overall_metadata)
            &&& self.main_table.allocator_inv()
            &&& self.item_table.inv(get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                                     self.overall_metadata.item_table_size as nat),
                                  self.overall_metadata, self.main_table@.valid_item_indices())
            &&& self.durable_list.inv(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                                       self.overall_metadata.list_area_size as nat),
                                    self.main_table@, self.overall_metadata)
            &&& PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list
            &&& Self::log_entries_do_not_modify_item_table(self.log@.physical_op_list, self.overall_metadata)
        }

        pub closed spec fn valid(self) -> bool 
        {
            let pm_view = self.wrpm@;
            &&& self.inv()
            &&& self.main_table.valid(get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat), self.overall_metadata)
            &&& self.item_table.valid(get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata,
                                    self.main_table@.valid_item_indices())
            &&& self.pending_alloc_inv()
        }

        pub closed spec fn log_entries_do_not_modify_item_table(op_log: Seq<AbstractPhysicalOpLogEntry>, overall_metadata: OverallMetadata) -> bool
        {
            forall |i: nat| i < op_log.len() ==> {
                let entry = #[trigger] op_log[i as int];
                ||| entry.absolute_addr + entry.len <= overall_metadata.item_table_addr
                ||| overall_metadata.item_table_addr + overall_metadata.item_table_size <= entry.absolute_addr
            }
        }

        pub closed spec fn pending_alloc_inv(self) -> bool
        {
            let durable_state_bytes = self.wrpm@.committed();
            let tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list);
            if let Some(tentative_state_bytes) = tentative_state_bytes {
                let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let tentative_main_table_region = extract_bytes(tentative_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size);
                let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size);
                &&& durable_main_table_view matches Some(durable_main_table_view)
                &&& tentative_main_table_view matches Some(tentative_main_table_view)
                &&& self.main_table.pending_alloc_inv(
                        durable_main_table_region,
                        tentative_main_table_region,
                        self.overall_metadata
                    )
                &&& self.item_table.pending_alloc_inv(
                        self.main_table@.valid_item_indices(),
                        durable_main_table_view.valid_item_indices(),
                        tentative_main_table_view.valid_item_indices(),
                    )
            } else {
                false
            } 
        }

        pub closed spec fn transaction_committed(self) -> bool
        {
            self.log@.op_list_committed
        }

        pub closed spec fn wrpm_view(self) -> PersistentMemoryRegionView
        {
            self.wrpm@
        }

        pub closed spec fn spec_overall_metadata(self) -> OverallMetadata
        {
            self.overall_metadata
        }

        pub closed spec fn spec_version_metadata(self) -> VersionMetadata
        {
            self.version_metadata
        }

        pub closed spec fn spec_overall_metadata_addr(self) -> u64
        {
            self.version_metadata.overall_metadata_addr
        }

        pub exec fn get_overall_metadata(&self) -> (out: OverallMetadata)
            ensures 
                out == self.spec_overall_metadata()
        {
            self.overall_metadata
        }

        pub closed spec fn spec_num_log_entries_in_current_transaction(self) -> nat 
        {
            self.log@.physical_op_list.len()
        }

        // In physical recovery, we blindly replay the physical log obtained by recovering the op log onto the rest of the
        // persistent memory region.
        pub open spec fn physical_recover(mem: Seq<u8>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>> {
            if mem.len() != overall_metadata.region_size {
                None
            } else {
            match UntrustedOpLog::<K, L>::recover(mem, version_metadata, overall_metadata) {
                Some(recovered_log) => Self::physical_recover_given_log(mem, overall_metadata, recovered_log),
                None => None,
            }
        }
        }

        pub open spec fn physical_recover_after_committing_log(mem: Seq<u8>, overall_metadata: OverallMetadata, oplog: AbstractOpLogState) -> Option<DurableKvStoreView<K, I, L>> {
            Self::physical_recover_given_log(mem, overall_metadata, oplog.commit_op_log())
        }

        pub open spec fn physical_recover_given_log(mem: Seq<u8>, overall_metadata: OverallMetadata, recovered_log: AbstractOpLogState) -> Option<DurableKvStoreView<K, I, L>> {
            let physical_log_entries = recovered_log.physical_op_list;
            let mem_with_log_installed = Self::apply_physical_log_entries(mem, physical_log_entries);
            if let Some(mem_with_log_installed) = mem_with_log_installed {
                Self::physical_recover_after_applying_log(mem_with_log_installed, overall_metadata, recovered_log)
            } else {
                None
            }
        }

        pub open spec fn physical_recover_after_applying_log(mem_with_log_installed: Seq<u8>, overall_metadata: OverallMetadata, recovered_log: AbstractOpLogState) -> Option<DurableKvStoreView<K, I, L>>
        {
            let main_table_region = extract_bytes(mem_with_log_installed, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
            let item_table_region = extract_bytes(mem_with_log_installed, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
            let list_area_region = extract_bytes(mem_with_log_installed, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);

            let main_table_view = parse_main_table::<K>(
                main_table_region, 
                overall_metadata.num_keys,
                overall_metadata.main_table_entry_size
            );
            if let Some(main_table_view) = main_table_view {
                let item_table_view = parse_item_table::<I, K>(
                    item_table_region,
                    overall_metadata.num_keys as nat,
                    main_table_view.valid_item_indices()
                );
                if let Some(item_table_view) = item_table_view {
                    let list_view = DurableList::<K, L>::parse_all_lists(
                        main_table_view,
                        list_area_region,
                        overall_metadata.list_node_size,
                        overall_metadata.num_list_entries_per_node
                    );
                    if let Some(list_view) = list_view {
                            Some(Self::recover_from_component_views(main_table_view, item_table_view, list_view))
                    } else {
                        None
                    }
                } else { 
                    None
                }
            } else {
                None
            }
        }

        // pub open spec fn apply_physical_log_entries(mem: Seq<u8>, physical_log_entries: Seq<AbstractPhysicalOpLogEntry>) -> Option<Seq<u8>>
        //     decreases physical_log_entries.len()
        // {
        //     if physical_log_entries.len() == 0 {
        //         Some(mem)
        //     } else {
        //         // Update the bytes indicated in the log entry
        //         match Self::apply_physical_log_entry(mem, physical_log_entries[0]) {
        //             Some(mem) => Self::apply_physical_log_entries(mem, physical_log_entries.drop_first()),
        //             None => None,
        //         }
        //     }
        // }

        pub open spec fn apply_physical_log_entries(mem: Seq<u8>, physical_log_entries: Seq<AbstractPhysicalOpLogEntry>) -> Option<Seq<u8>>
            decreases physical_log_entries.len()
        {
            if physical_log_entries.len() == 0 {
                Some(mem)
            } else {
                let prefix = physical_log_entries.subrange(0, physical_log_entries.len() - 1);
                let last_op = physical_log_entries[physical_log_entries.len() - 1];
                if let Some(new_mem) = Self::apply_physical_log_entries(mem, prefix) {
                    Self::apply_physical_log_entry(new_mem, last_op)
                } else {
                    None
                }
            }
        }

        pub open spec fn apply_physical_log_entry(mem: Seq<u8>, log_op: AbstractPhysicalOpLogEntry) -> Option<Seq<u8>>
        {
            if {
                ||| log_op.absolute_addr + log_op.len > mem.len() 
                ||| log_op.bytes.len() != log_op.len
            } {
                // Return None if the log_op is ill-formed
                None
            } else {
                Some(mem.map(|pos: int, pre_byte: u8| 
                    if log_op.absolute_addr <= pos < log_op.absolute_addr + log_op.len {
                        log_op.bytes[pos - log_op.absolute_addr]
                    } else {
                        pre_byte
                    }
                ))
            }
        }

        pub closed spec fn phys_log_entry_corresponds_to_logical_log_entry(
            mem: Seq<u8>, 
            phys_entry: AbstractPhysicalOpLogEntry,
            logical_entry: LogicalOpLogEntry<L>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        ) -> bool 
        {
            let pre_replay_kvstore_state = Self::physical_recover(mem, version_metadata, overall_metadata);
            // applying the physical log entry and the logical log entry should result in the 
            // same recovery state
            let phys_replay_state = Self::apply_physical_log_entry(mem, phys_entry);
            if let Some(phys_replay_state) = phys_replay_state {
                let log_replay_state = if logical_entry matches LogicalOpLogEntry::UpdateListElement{..} {
                    DurableList::<K, L>::apply_log_op_to_list_node_mem(mem, overall_metadata.list_node_size, logical_entry)
                } else {
                    MainTable::<K>::apply_log_op_to_main_table_mem(mem, logical_entry)
                };
                phys_replay_state == log_replay_state
            } else {
                false
            }
        }

        pub closed spec fn phys_log_corresponds_to_logical_log(
            mem: Seq<u8>,
            phys_log: Seq<AbstractPhysicalOpLogEntry>,
            logical_log: Seq<LogicalOpLogEntry<L>>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        ) -> bool
            decreases phys_log.len() 
        {
            if phys_log.len() != logical_log.len() {
                false
            } else if phys_log.len() == 0 {
                true
            } else {
                let phys_entry = phys_log[0];
                let logical_entry = logical_log[0];
                if !Self::phys_log_entry_corresponds_to_logical_log_entry(mem, phys_entry, logical_entry, version_metadata, overall_metadata) {
                    false 
                } else {
                    let new_mem = Self::apply_physical_log_entry(mem, phys_entry);
                    if let Some(new_mem) = new_mem {
                        Self::phys_log_corresponds_to_logical_log(new_mem, phys_log.drop_first(), logical_log.drop_first(), version_metadata, overall_metadata)
                    } else {
                        false
                    }
                }
            }
        }

        // This lemma proves that after `tentatively_append_log_entry` fails and begins to abort the 
        // current transaction, replaying the log is a no op and we can still recover to a valid state.
        // This satisfies the preconditions for the individual components' abort functions, which
        // will reestablish their invariants before returning an error to the caller.
        proof fn lemma_transaction_abort(self, old_self: Self)
            requires
                old_self.inv(),
                self.overall_metadata == old_self.overall_metadata,
                self.wrpm@.len() == self.overall_metadata.region_size,
                self.wrpm@.len() >= VersionMetadata::spec_size_of(),
                !old_self.transaction_committed(),
                self.wrpm@.len() == old_self.wrpm@.len(),
                self.wrpm@.no_outstanding_writes(),
                0 < self.version_metadata.overall_metadata_addr < 
                    self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() <
                    self.overall_metadata.log_area_addr,
                0 < VersionMetadata::spec_size_of() < self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() < self.wrpm@.len(),
                forall |s| #[trigger] old_self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(old_self@),
                UntrustedOpLog::<K, L>::recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                views_differ_only_in_log_region(old_self.wrpm@.flush(), self.wrpm@, 
                    self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                old_self.main_table@.valid_item_indices() == self.main_table@.valid_item_indices(),
            ensures
                ({
                    let main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);      
                    forall |s| #[trigger] main_table_subregion_view.can_crash_as(s) ==> 
                        parse_main_table::<K>(s, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(old_self.main_table@)
                }),
                ({
                    let old_item_table_subregion_view = get_subregion_view(old_self.wrpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat); 
                    let item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);      
                    &&& forall |s| #[trigger] item_table_subregion_view.can_crash_as(s) ==> 
                            parse_item_table::<I, K>(s, self.overall_metadata.num_keys as nat,
                                                     self.main_table@.valid_item_indices())
                        == Some(old_self.item_table@)
                    &&& old_item_table_subregion_view.can_crash_as(item_table_subregion_view.committed())
                }),
                Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) is Some,
        {
            let main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
            assert(item_table_subregion_view.can_crash_as(item_table_subregion_view.committed()));
            assert(list_area_subregion_view.can_crash_as(list_area_subregion_view.committed()));
    
            let old_main_table_subregion_view = get_subregion_view(old_self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let old_item_table_subregion_view = get_subregion_view(old_self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let old_list_area_subregion_view = get_subregion_view(old_self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);
    
            // All crash states of the old pm state recover to the current abstract state; since self.wrpm@.flush().committed()
            // is a crash state of self.wrpm@, the current PM also recovers to the current abstract state. 
            assert(old_main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
            assert(old_item_table_subregion_view.can_crash_as(item_table_subregion_view.committed()));
            assert(old_list_area_subregion_view.can_crash_as(list_area_subregion_view.committed()));

            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(main_table_subregion_view);
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(old_item_table_subregion_view);
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(item_table_subregion_view);
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(list_area_subregion_view);
            assert(forall |s| main_table_subregion_view.can_crash_as(s) ==> s == main_table_subregion_view.committed());
            assert(forall |s| item_table_subregion_view.can_crash_as(s) ==> s == item_table_subregion_view.committed());
            assert(forall |s| list_area_subregion_view.can_crash_as(s) ==> s == list_area_subregion_view.committed());
    
            let recovered_op_log = UntrustedOpLog::<K, L>::recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata).unwrap();
            let mem_with_log_installed = Self::apply_physical_log_entries(self.wrpm@.committed(), recovered_op_log.physical_op_list).unwrap();
            let main_table_region_view_with_log_installed = extract_bytes(mem_with_log_installed, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);   
            let item_table_region_view_with_log_installed = extract_bytes(mem_with_log_installed, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let list_area_region_view_with_log_installed = extract_bytes(mem_with_log_installed, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat); 
            assert(main_table_region_view_with_log_installed == main_table_subregion_view.committed());
            assert(item_table_region_view_with_log_installed == item_table_subregion_view.committed());
            assert(list_area_region_view_with_log_installed == list_area_subregion_view.committed());
    
            assert(forall |s| #[trigger] main_table_subregion_view.can_crash_as(s) ==> 
                parse_main_table::<K>(s, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(old_self.main_table@));
            assert(forall |idx: u64| old_self.main_table.allocator_view().contains(idx) ==> idx < self.overall_metadata.num_keys);

            assert(Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) is Some);
        }

        pub proof fn lemma_metadata_unchanged_when_views_differ_only_in_log_region(
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires
                views_differ_only_in_log_region(v1.flush(), v2, 
                    overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
                version_metadata == deserialize_version_metadata(v1.committed()),
                overall_metadata == deserialize_overall_metadata(v1.committed(), version_metadata.overall_metadata_addr),
                v2.no_outstanding_writes(),
                no_outstanding_writes_to_version_metadata(v1),
                no_outstanding_writes_to_overall_metadata(v1, version_metadata.overall_metadata_addr as int),
                0 < version_metadata.overall_metadata_addr < 
                    version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() <
                    overall_metadata.log_area_addr,
                0 < VersionMetadata::spec_size_of() < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() < v1.len(),
                v1.len() == v2.len(),
                v1.len() >= VersionMetadata::spec_size_of(),
                v1.len() == overall_metadata.region_size,
            ensures 
                version_metadata == deserialize_version_metadata(v2.committed()),
                overall_metadata == deserialize_overall_metadata(v2.committed(), version_metadata.overall_metadata_addr),
        {
            lemma_establish_extract_bytes_equivalence(v1.committed(), v2.committed());
            lemma_establish_extract_bytes_equivalence(v1.flush().committed(), v2.committed());
            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(v1);

            assert(version_metadata == deserialize_version_metadata(v1.committed()));
            assert(overall_metadata == deserialize_overall_metadata(v1.committed(), version_metadata.overall_metadata_addr));

            assert(extract_version_metadata(v1.committed()) == extract_version_metadata(v2.committed()));
            assert(extract_overall_metadata(v1.committed(), version_metadata.overall_metadata_addr) == 
                extract_overall_metadata(v2.committed(), version_metadata.overall_metadata_addr));

            assert(version_metadata == deserialize_version_metadata(v1.flush().committed()));
            assert(overall_metadata == deserialize_overall_metadata(v1.flush().committed(), version_metadata.overall_metadata_addr));
        }

        pub proof fn lemma_applying_same_log_preserves_states_differ_only_in_log_region(
            mem1: Seq<u8>,
            mem2: Seq<u8>,
            op_log: Seq<AbstractPhysicalOpLogEntry>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata
        )
            requires
                states_differ_only_in_log_region(mem1, mem2, overall_metadata.log_area_addr as nat,
                    overall_metadata.log_area_size as nat),
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                overall_metadata.log_area_size <= mem1.len(),
                AbstractPhysicalOpLogEntry::log_inv(op_log, version_metadata, overall_metadata),
            ensures 
                ({
                    let mem1_with_log = Self::apply_physical_log_entries(mem1, op_log);
                    let mem2_with_log = Self::apply_physical_log_entries(mem2, op_log);
                    &&& mem1_with_log matches Some(mem1_with_log)
                    &&& mem2_with_log matches Some(mem2_with_log)
                    &&& states_differ_only_in_log_region(mem1_with_log, mem2_with_log, overall_metadata.log_area_addr as nat,
                            overall_metadata.log_area_size as nat)
                })
        {
            Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(mem1, version_metadata, overall_metadata, op_log);
            Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(mem2, version_metadata, overall_metadata, op_log);
            Self::lemma_log_replay_preserves_size(mem1, op_log);
            Self::lemma_log_replay_preserves_size(mem2, op_log);


            let mem1_with_log = Self::apply_physical_log_entries(mem1, op_log).unwrap();
            let mem2_with_log = Self::apply_physical_log_entries(mem2, op_log).unwrap();

            assert forall |addr: int| {
                &&& 0 <= addr < mem1.len() 
                &&& !(overall_metadata.log_area_addr <= addr < overall_metadata.log_area_addr + overall_metadata.log_area_size)
            } implies mem1_with_log[addr] == #[trigger] mem2_with_log[addr] by {
                Self::lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, op_log);
            }
        }

        pub proof fn lemma_log_area_unchanged_by_applying_log_entries(
            mem: Seq<u8>,
            op_log: Seq<AbstractPhysicalOpLogEntry>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires 
                mem.len() == overall_metadata.region_size,
                overall_metadata.log_area_size <= mem.len(),
                AbstractPhysicalOpLogEntry::log_inv(op_log, version_metadata, overall_metadata),
                Self::apply_physical_log_entries(mem, op_log) is Some,
            ensures 
                ({
                    let mem_with_log_installed = Self::apply_physical_log_entries(mem, op_log).unwrap();
                    forall |addr: int| {
                        &&& 0 <= addr < mem.len() 
                        &&& overall_metadata.log_area_addr <= addr < overall_metadata.log_area_addr + overall_metadata.log_area_size
                    } ==> mem_with_log_installed[addr] == #[trigger] mem[addr] 
                })
        {
            let mem_with_log_installed = Self::apply_physical_log_entries(mem, op_log).unwrap();

            assert(forall |addr: int| {
                &&& 0 <= addr < mem.len() 
                &&& overall_metadata.log_area_addr <= addr < overall_metadata.log_area_addr + overall_metadata.log_area_size
            } ==> !addr_modified_by_recovery(op_log, addr));

            assert forall |addr: int| {
                &&& 0 <= addr < mem.len() 
                &&& !addr_modified_by_recovery(op_log, addr)
            } implies mem_with_log_installed[addr] == mem[addr] by {
                Self::lemma_byte_unchanged_by_log_replay(addr, mem, version_metadata, overall_metadata, op_log);
            }
        }

        pub proof fn lemma_item_table_bytes_unchanged_by_applying_log_entries(
            mem: Seq<u8>,
            op_log: Seq<AbstractPhysicalOpLogEntry>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires 
                mem.len() == overall_metadata.region_size,
                overall_metadata.log_area_size <= mem.len(),
                AbstractPhysicalOpLogEntry::log_inv(op_log, version_metadata, overall_metadata),
                Self::apply_physical_log_entries(mem, op_log) is Some,
                Self::log_entries_do_not_modify_item_table(op_log, overall_metadata),
            ensures 
                ({
                    let mem_with_log_installed = Self::apply_physical_log_entries(mem, op_log).unwrap();
                    forall |addr: int| {
                        &&& 0 <= addr < mem.len() 
                        &&& overall_metadata.item_table_addr <= addr < overall_metadata.item_table_addr + overall_metadata.item_table_size
                    } ==> mem_with_log_installed[addr] == #[trigger] mem[addr] 
                })
        {
            let mem_with_log_installed = Self::apply_physical_log_entries(mem, op_log).unwrap();

            assert(forall |addr: int| {
                &&& 0 <= addr < mem.len() 
                &&& overall_metadata.item_table_addr <= addr < overall_metadata.item_table_addr + overall_metadata.item_table_size
            } ==> !addr_modified_by_recovery(op_log, addr));

            assert forall |addr: int| {
                &&& 0 <= addr < mem.len() 
                &&& !addr_modified_by_recovery(op_log, addr)
            } implies mem_with_log_installed[addr] == mem[addr] by {
                Self::lemma_byte_unchanged_by_log_replay(addr, mem, version_metadata, overall_metadata, op_log);
            }
        }

        pub proof fn lemma_byte_unchanged_by_log_replay(
            addr: int,
            mem: Seq<u8>, 
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            op_log: Seq<AbstractPhysicalOpLogEntry>,
        )
            requires 
                mem.len() == overall_metadata.region_size,
                overall_metadata.log_area_size <= mem.len(),
                AbstractPhysicalOpLogEntry::log_inv(op_log, version_metadata, overall_metadata),
                Self::apply_physical_log_entries(mem, op_log) is Some,
                !addr_modified_by_recovery(op_log, addr),
                0 <= addr < mem.len(),
            ensures 
                ({
                    let mem_with_log_installed = Self::apply_physical_log_entries(mem, op_log).unwrap();
                    mem_with_log_installed[addr] == mem[addr] 
                })
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                // trivial
            } else {
                let prefix = op_log.subrange(0, op_log.len() - 1);
                let last_op = op_log[op_log.len() - 1];
                let mem_with_prefix = Self::apply_physical_log_entries(mem, prefix).unwrap();
                Self::lemma_log_replay_preserves_size(mem, prefix);
                Self::lemma_byte_unchanged_by_log_replay(addr, mem, version_metadata, overall_metadata, prefix);
            }
        }

        pub proof fn lemma_log_replay_preserves_size(
            mem: Seq<u8>, 
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        ) 
            requires
                Self::apply_physical_log_entries(mem, phys_log) is Some 
            ensures
                ({ 
                    let replay_mem = Self::apply_physical_log_entries(mem, phys_log).unwrap();
                    replay_mem.len() == mem.len()
                })
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial
            } else {
                Self::lemma_log_replay_preserves_size(mem, phys_log.subrange(0, phys_log.len() - 1));
            }
        }

        // This lemma proves that replaying a log of valid entries will always result in a Some return value
        pub proof fn lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
            mem: Seq<u8>, 
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        )
            requires 
                AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
                mem.len() == overall_metadata.region_size,
                overall_metadata.log_area_size <= mem.len(),
            ensures 
                Self::apply_physical_log_entries(mem, phys_log) is Some,
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial -- empty log always returns Some
            } else {
                let prefix = phys_log.subrange(0, phys_log.len() - 1);
                let last_op = phys_log[phys_log.len() - 1];
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
                    mem,
                    version_metadata,
                    overall_metadata,
                    phys_log.subrange(0, phys_log.len() - 1),
                );
                Self::lemma_log_replay_preserves_size(mem, prefix);
            }
        }

        pub proof fn lemma_mem_equal_after_recovery(
            mem1: Seq<u8>, 
            mem2: Seq<u8>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>, 
        )
            requires
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                Self::apply_physical_log_entries(mem1, phys_log) is Some,
                Self::apply_physical_log_entries(mem2, phys_log) is Some,
                AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
                forall |i: int| 0 <= i < mem1.len() && mem1[i] != mem2[i] ==> addr_modified_by_recovery(phys_log, i),
            ensures
                ({
                    let replay1 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
                    let replay2 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();
                    replay1 == replay2
                })
            decreases phys_log.len()
        {
            let replay1 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
            let replay2 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();

            Self::lemma_log_replay_preserves_size(mem1, phys_log);
            Self::lemma_log_replay_preserves_size(mem2, phys_log);

            assert_seqs_equal!(replay1 == replay2, addr => {
                Self::lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, phys_log);
            });
        }

        pub proof fn lemma_byte_equal_after_recovery_specific_byte(
            addr: int,
            mem1: Seq<u8>, 
            mem2: Seq<u8>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            phys_log: Seq<AbstractPhysicalOpLogEntry>,
        )
            requires
                mem1.len() == mem2.len(),
                mem1.len() == overall_metadata.region_size,
                Self::apply_physical_log_entries(mem1, phys_log) is Some,
                Self::apply_physical_log_entries(mem2, phys_log) is Some,
                AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
                mem1[addr] == mem2[addr] || addr_modified_by_recovery(phys_log, addr),
                0 <= addr < mem1.len(),
            ensures
                ({
                    let replay1 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem1, phys_log).unwrap();
                    let replay2 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(mem2, phys_log).unwrap();
                    replay1[addr] == replay2[addr]
                })
            decreases phys_log.len()
        {
            if phys_log.len() == 0 {
                // trivial
            } else {
                let prefix = phys_log.subrange(0, phys_log.len() - 1);
                let last_op = phys_log[phys_log.len() - 1];
                let mem1_with_prefix = Self::apply_physical_log_entries(mem1, prefix).unwrap();
                let mem2_with_prefix = Self::apply_physical_log_entries(mem2, prefix).unwrap();
                Self::lemma_log_replay_preserves_size(mem1, prefix);
                Self::lemma_log_replay_preserves_size(mem2, prefix);

                if mem1[addr] == mem2[addr] || addr_modified_by_recovery(prefix, addr)  {
                    Self::lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, prefix);
                } else if (mem1_with_prefix[addr] != mem2_with_prefix[addr]) {
                    // According to the definition of addr_modified_by_recovery, there exists a log entry
                    // in phys_log that modifies this address. We have proven that the log entry cannot be 
                    // in prefix.Verus can easily prove that applying the log entry that modifies the address 
                    // will make the byte match in both mems, but we have to convince it that it must be 
                    // the last op by proving that this is the only op that is not in the prefix.
                    assert(forall |i: int| 0 <= i < prefix.len() ==> prefix[i] == phys_log[i]);
                }
                // else, trivial
            }
        }

        proof fn lemma_tentative_log_entry_append_is_crash_safe(
            self,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            perm: &Perm
        )
            requires
                self.inv(),
                !self.transaction_committed(),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@),
                forall |s| {
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                } ==> #[trigger] perm.check_permission(s),
                Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == Some(self@),
                no_outstanding_writes_to_version_metadata(self.wrpm@),
                no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int),
                self.wrpm@.len() >= VersionMetadata::spec_size_of(),
                Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list) is Some,
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) <==> crash_pred(s),
            ensures
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                } ==> #[trigger] crash_pred(s2),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                        UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
    
        {
            self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
    
            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);

            assert forall |s| #[trigger] self.wrpm@.can_crash_as(s) implies 
                Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                    UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
            by {
                self.log.lemma_if_not_committed_recovery_equals_drop_pending_appends(self.wrpm, s, self.version_metadata, self.overall_metadata);
            }
    
            assert forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
            } implies #[trigger] crash_pred(s2) by {
                
                // Caller has permission to crash into s1. 
                // We don't change anything but the log, and the log state stays the same, then we stay in the same state.
                // It doesn't actually matter what s1 recovers to, just that it is legal.
    
                let recovered_log = AbstractOpLogState::initialize();
                let mem_with_log_installed_s1 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(s1, recovered_log.physical_op_list).unwrap();
                assert(mem_with_log_installed_s1 == s1);
                let mem_with_log_installed_s2 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
                assert(mem_with_log_installed_s2 == s2);
                
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    mem_with_log_installed_s1, mem_with_log_installed_s2, self.version_metadata, self.overall_metadata);
    
                assert(Self::physical_recover(s1, self.version_metadata, self.overall_metadata) == Some(self@));
                assert(Self::physical_recover(s2, self.version_metadata, self.overall_metadata) == Some(self@));
            }
        }

        // This has to be callable during `start` when we don't have a DurableKvStore yet,
        // so it cannot take a `self` argument.
        proof fn lemma_clear_log_is_crash_safe(
            wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            op_log: UntrustedOpLog<K, L>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            state: DurableKvStoreView<K, I, L>,
            perm: &Perm
        )
            requires 
                op_log.inv(wrpm_region@, version_metadata, overall_metadata),
                op_log@.op_list_committed,
                forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==> 
                    UntrustedOpLog::<K, L>::recover(s, version_metadata, overall_metadata) == Some(op_log@),
                UntrustedOpLog::<K, L>::recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(op_log@),
                Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(state),
                wrpm_region@.no_outstanding_writes(),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s| (Self::physical_recover(s, version_metadata, overall_metadata) == Some(state)) <==> crash_pred(s),
                wrpm_region@.len() >= VersionMetadata::spec_size_of(),
                overall_metadata.list_area_addr + overall_metadata.list_area_size <= wrpm_region@.len(),
                wrpm_region@.len() == overall_metadata.region_size,
                AbstractPhysicalOpLogEntry::log_inv(op_log@.physical_op_list, version_metadata, overall_metadata),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == 
                    Self::physical_recover_given_log(wrpm_region@.committed(), overall_metadata, AbstractOpLogState::initialize()),
            ensures 
                forall |s2: Seq<u8>| {
                    let current_state = wrpm_region@.flush().committed();
                    &&& current_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(s2, current_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                    &&& {
                            ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
                            ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                        }
                } ==> #[trigger] crash_pred(s2),
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, version_metadata, overall_metadata) == Some(op_log@)
                    &&& UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
                } ==> #[trigger] crash_pred(s2)
        {
            assert(forall |s| #[trigger] wrpm_region@.can_crash_as(s) ==>
                Self::physical_recover(s, version_metadata, overall_metadata) == Some(state) ==> {
                    ||| UntrustedOpLog::<K, L>::recover(s, version_metadata, overall_metadata) == Some(op_log@)
                    ||| UntrustedOpLog::<K, L>::recover(s, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                }
            );

            assert forall |s2: Seq<u8>| {
                let current_state = wrpm_region@.flush().committed();
                &&& current_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(s2, current_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                &&& {
                        ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
                        ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                    }
            } implies #[trigger] crash_pred(s2) by {
                let current_state = wrpm_region@.flush().committed();
                lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(wrpm_region@);
                assert(wrpm_region@.can_crash_as(current_state));
                if UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@) {
                    // The clear log op did not complete before the crash. In this case, we recover the full log  
                    Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                        current_state, s2, op_log@.physical_op_list, version_metadata, overall_metadata);
                    let current_state_with_log_installed = Self::apply_physical_log_entries(current_state, op_log@.physical_op_list).unwrap();
                    let s2_with_log_installed = Self::apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                    Self::lemma_log_replay_preserves_size(current_state, op_log@.physical_op_list);
                    Self::lemma_log_replay_preserves_size(s2, op_log@.physical_op_list);

                    assert(states_differ_only_in_log_region(current_state_with_log_installed, s2_with_log_installed, 
                        overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        current_state_with_log_installed, s2_with_log_installed, version_metadata, overall_metadata);
                    
                    assert(Self::physical_recover(current_state, version_metadata, overall_metadata) == Some(state));
                    assert(Self::physical_recover(s2, version_metadata, overall_metadata) == Some(state));
                } else {
                    // the log was cleared before the crash
                    assert(UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize()));

                    let recovered_log = AbstractOpLogState::initialize();
                    let current_state_with_log_installed = Self::apply_physical_log_entries(current_state, recovered_log.physical_op_list).unwrap();
                    assert(current_state_with_log_installed == current_state);
                    let s2_with_log_installed = Self::apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
                    assert(s2_with_log_installed == s2);
                    Self::lemma_log_replay_preserves_size(current_state, recovered_log.physical_op_list);
                    Self::lemma_log_replay_preserves_size(s2, recovered_log.physical_op_list);

                    assert(states_differ_only_in_log_region(current_state_with_log_installed, s2_with_log_installed, 
                        overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        current_state_with_log_installed, s2_with_log_installed, version_metadata, overall_metadata);
                }
            }

            assert forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                &&& UntrustedOpLog::<K, L>::recover(s1, version_metadata, overall_metadata) == Some(op_log@)
                &&& UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
            } implies #[trigger] crash_pred(s2) by {
                // In this case, the log was not durably cleared before the crash, so the log recovers to its old state
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s1, version_metadata, overall_metadata, op_log@.physical_op_list);
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s2, version_metadata, overall_metadata, op_log@.physical_op_list);
                Self::lemma_log_replay_preserves_size(s1, op_log@.physical_op_list);
                Self::lemma_log_replay_preserves_size(s2, op_log@.physical_op_list);

                // For this crash pre condition, we'll prove that recovering from s1_with_log_installed's non-log components plus op_log (which we already 
                // know is the recovery state of its op log) is equivalent to recovering normally from s1 (which we already know, from crash_pred(s1), gives
                // Some(state)). Then, we prove that s2 has the same non-log components after replaying op_log (which we already know is also the recovery state
                // of its op log) as s1, which tells us that they recover to the same DurableKvStore state.
                let s1_with_log_installed = Self::apply_physical_log_entries(s1, op_log@.physical_op_list).unwrap();
                let main_table_region = extract_bytes(s1_with_log_installed, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let item_table_region = extract_bytes(s1_with_log_installed, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let list_area_region = extract_bytes(s1_with_log_installed, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                let main_table_view = parse_main_table::<K>(
                    main_table_region, 
                    overall_metadata.num_keys,
                    overall_metadata.main_table_entry_size
                ).unwrap();
                let item_table_view = parse_item_table::<I, K>(
                    item_table_region,
                    overall_metadata.num_keys as nat,
                    main_table_view.valid_item_indices()
                ).unwrap();
                let list_view = DurableList::<K, L>::parse_all_lists(
                    main_table_view,
                    list_area_region,
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node
                ).unwrap();
                assert(Some(Self::recover_from_component_views(main_table_view, item_table_view, list_view)) == 
                    Self::physical_recover(s1, version_metadata, overall_metadata));
                let s2_with_log_installed = Self::apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                    s1, s2, op_log@.physical_op_list, version_metadata, overall_metadata);
                let s2_with_log_installed = Self::apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    s1_with_log_installed, s2_with_log_installed, version_metadata, overall_metadata);
                assert(Some(Self::recover_from_component_views(main_table_view, item_table_view, list_view)) == 
                    Self::physical_recover(s2, version_metadata, overall_metadata));
            }
        }

        proof fn lemma_version_and_overall_metadata_unchanged(
            self,
            old_pm_view: PersistentMemoryRegionView
        )
            requires 
                0 < self.version_metadata.overall_metadata_addr < 
                    self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() <
                    self.overall_metadata.log_area_addr,
                self.wrpm@.len() == old_pm_view.len(),
                self.wrpm@.no_outstanding_writes(),
                0 < VersionMetadata::spec_size_of() < self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() < self.wrpm@.len(),
                no_outstanding_writes_to_version_metadata(old_pm_view),
                no_outstanding_writes_to_overall_metadata(old_pm_view, self.version_metadata.overall_metadata_addr as int),
                version_and_overall_metadata_match::<K, L>(old_pm_view.committed(), self.wrpm@.committed(), self.version_metadata.overall_metadata_addr as nat),
                self.version_metadata == deserialize_version_metadata(old_pm_view.committed()),
                self.overall_metadata == deserialize_overall_metadata(old_pm_view.committed(), self.version_metadata.overall_metadata_addr ),
            ensures 
                self.version_metadata == deserialize_version_metadata(self.wrpm@.committed()),
                self.overall_metadata == deserialize_overall_metadata(self.wrpm@.committed(), self.version_metadata.overall_metadata_addr),
        {
            broadcast use pmcopy_axioms;
            let pm_view = self.wrpm@;
            let mem = pm_view.committed();
            let flushed_old_mem = old_pm_view.flush().committed();

            lemma_establish_extract_bytes_equivalence(mem, flushed_old_mem);
            assert(extract_bytes(mem, 0, VersionMetadata::spec_size_of()) == 
                extract_bytes(flushed_old_mem, 0, VersionMetadata::spec_size_of()));
            assert(extract_bytes(flushed_old_mem, 0, VersionMetadata::spec_size_of()) == 
                extract_bytes(old_pm_view.committed(), 0, VersionMetadata::spec_size_of()));

            assert(extract_bytes(mem, self.version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()) == 
                extract_bytes(flushed_old_mem, self.version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()));
            assert(extract_bytes(flushed_old_mem, self.version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()) =~= 
                extract_bytes(old_pm_view.committed(), self.version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()));
            assert(self.overall_metadata == deserialize_overall_metadata(old_pm_view.committed(), self.version_metadata.overall_metadata_addr));
            assert(self.overall_metadata == deserialize_overall_metadata(flushed_old_mem, self.version_metadata.overall_metadata_addr));
            assert(self.overall_metadata == deserialize_overall_metadata(mem, self.version_metadata.overall_metadata_addr));
        }

        proof fn lemma_durable_kv_satisfies_crash_condition_with_init_op_log(
            self,
            s1: Seq<u8>,
            s2: Seq<u8>,
            crash_pred: spec_fn(Seq<u8>) -> bool,
        )
            requires
                self.valid(),
                !self.transaction_committed(),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> crash_pred(s),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@),
                s1.len() == s2.len(),
                crash_pred(s1),
                states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat,
                    self.overall_metadata.log_area_size as nat),
                UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                forall |s|{
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == self.tentative_view()
                } ==> crash_pred(s),
                no_outstanding_writes_to_version_metadata(self.wrpm@),
                no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int),
                self.wrpm@.len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = self.tentative_view();
                    tentative_view is Some
                }),
                self.spec_num_log_entries_in_current_transaction() > 0,
                ({
                    ||| Self::physical_recover(s1, self.version_metadata, self.overall_metadata) == Some(self@)
                    ||| Self::physical_recover(s1, self.version_metadata, self.overall_metadata) == self.tentative_view()
                })
            ensures 
                crash_pred(s2)
        {
            lemma_establish_extract_bytes_equivalence(s1, s2);
            self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list).unwrap();
            Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);

            let recovered_log = AbstractOpLogState::initialize();
            let mem_with_log_installed_s1 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(s1, recovered_log.physical_op_list).unwrap();
            assert(mem_with_log_installed_s1 == s1);
            let mem_with_log_installed_s2 = DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
            assert(mem_with_log_installed_s2 == s2);

            lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                mem_with_log_installed_s1, mem_with_log_installed_s2, self.version_metadata, self.overall_metadata);
            
            // s2 actually can't recover to self.tentative_view() in this case, but we don't need to prove that;
            // we just need to prove that all of its crash states are allowed by crash_pred
            assert({
                ||| Self::physical_recover(s2, self.version_metadata, self.overall_metadata) == Some(self@)
                ||| Self::physical_recover(s2, self.version_metadata, self.overall_metadata) == self.tentative_view()
            });
        }

        // In logical recovery, we replay logical log entries based on replay functions provided by each component
        // TODO: might be useful to return mem from here?
        pub open spec fn logical_recover(mem: Seq<u8>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>> 
        {
            let recovered_log = UntrustedOpLog::<K, L>::recover(mem, version_metadata, overall_metadata);
            if let Some(recovered_log) = recovered_log {
                let logical_log_entries = choose |logical_log: Seq<LogicalOpLogEntry<L>>| 
                    Self::phys_log_corresponds_to_logical_log(mem, recovered_log.physical_op_list, logical_log, version_metadata, overall_metadata);
                // recover main table from logical log
                let main_table_region = extract_bytes(mem, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let main_table_region = MainTable::<K>::spec_replay_log_main_table(main_table_region, logical_log_entries);
                let main_table_view = parse_main_table::<K>(
                    main_table_region, 
                    overall_metadata.num_keys,
                    overall_metadata.main_table_entry_size
                );
                if let Some(main_table_view) = main_table_view {
                    // recover item table. This does not involve the logical log, so we can just directly parse it
                    let item_table_region = extract_bytes(mem, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                    let item_table_view = parse_item_table::<I, K>(
                        item_table_region,
                        overall_metadata.num_keys as nat,
                        main_table_view.valid_item_indices()
                    );
                    if let Some(item_table_view) = item_table_view {
                        // recover the list area from logical log
                        let list_area_region = extract_bytes(mem, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                        let list_area_region = DurableList::<K, L>::replay_log_list_nodes(list_area_region, overall_metadata.list_node_size, logical_log_entries);
                        let list_view = DurableList::<K, L>::parse_all_lists(
                            main_table_view,
                            list_area_region,
                            overall_metadata.list_node_size,
                            overall_metadata.num_list_entries_per_node
                        );
                        if let Some(list_view) = list_view {
                            Some(Self::recover_from_component_views(main_table_view, item_table_view, list_view))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }

        // Note: this fn assumes that the item and list head in the main table entry point 
        // to valid entries in the corresponding structures.
        pub open spec fn recover_from_component_views(
            recovered_main_table: MainTableView<K>, 
            recovered_item_table: DurableItemTableView<I>,
            recovered_lists: DurableListView<K, L>
        ) -> DurableKvStoreView<K, I, L>
        {
            let contents = Map::new(
                |i: int| 0 <= i < recovered_main_table.durable_main_table.len() && recovered_main_table.durable_main_table[i] is Some,
                |i: int| {
                    let main_table_entry = recovered_main_table.durable_main_table[i].unwrap();
                    let item_index = main_table_entry.item_index();
                    let list_head_index = main_table_entry.list_head_index();
                    let key = main_table_entry.key();
                    
                    let item = recovered_item_table.durable_item_table[item_index as int].unwrap();
                    let list_view = recovered_lists.durable_lists[key];
                    let list = DurableKvStoreList {
                            list: Seq::new(
                                    list_view.len(),
                                    |i: int| list_view[i].unwrap_valid().list_element()
                                )
                    };
                    DurableKvStoreViewEntry { key, item, list }
                }
            );
            DurableKvStoreView { contents }
        }

        pub exec fn get_elements_per_node(&self) -> u64 {
            self.durable_list.get_elements_per_node()
        }

        pub fn setup(
            pm_region: &mut PM,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            kvstore_id: u128,
        ) -> (result: Result<(), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(pm_region).inv(),
                old(pm_region)@.no_outstanding_writes(),
                overall_metadata.region_size == old(pm_region)@.len(),
                memory_correctly_set_up_on_region::<K, I, L>(old(pm_region)@.committed(), kvstore_id),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, kvstore_id),
           ensures 
                pm_region.inv(),
                match result {
                    Ok(()) => {
                        &&& Self::physical_recover(pm_region@.committed(), version_metadata, overall_metadata) matches Some(recovered_view)
                        &&& Self::physical_recover(pm_region@.committed(), version_metadata, overall_metadata) == Self::logical_recover(pm_region@.committed(), version_metadata, overall_metadata)
                        &&& recovered_view == DurableKvStoreView::<K, I, L>::init()
                    }
                    Err(_) => true
                }
        {
            let num_keys = overall_metadata.num_keys;
            let overall_metadata_addr = version_metadata.overall_metadata_addr;

            // Define subregions for each durable component and call setup on each one
            let ghost writable_addr_fn = |addr: int| true;
            let main_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.main_table_addr, 
                Ghost(overall_metadata.main_table_size as nat),
                Ghost(writable_addr_fn)
            );
            MainTable::<K>::setup::<PM, L>(&main_table_subregion, pm_region, num_keys, overall_metadata.main_table_entry_size)?;
            proof { main_table_subregion.lemma_reveal_opaque_inv(pm_region); }

            proof {
                let bytes = pm_region@.flush().committed();
                let main_table_bytes = extract_bytes(bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                assert(main_table_bytes == main_table_subregion.view(pm_region).flush().committed());
            }

            // Both the item table and list region do not require any writes in setup; we just need to prove that regardless of the contents of 
            // the PM in those areas, if we set up the item table correctly then 
            let item_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.item_table_addr, 
                Ghost(overall_metadata.item_table_size as nat),
                Ghost(writable_addr_fn)
            );
            proof { DurableItemTable::<K, I>::lemma_table_is_empty_at_setup::<PM, L>(&item_table_subregion, pm_region, Set::empty(), num_keys); }
            let list_area_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.list_area_addr, 
                Ghost(overall_metadata.list_area_size as nat),
                Ghost(writable_addr_fn)
            );
            proof { DurableList::<K, L>::lemma_list_is_empty_at_setup(&list_area_subregion, pm_region, AbstractOpLogState::initialize(), num_keys, 
                overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node, overall_metadata.num_list_nodes, MainTableView::<K>::init(num_keys)) }

            let ghost pre_log_setup_bytes = pm_region@.flush().committed();

            UntrustedLogImpl::setup::<PM, K>(pm_region, overall_metadata.log_area_addr, overall_metadata.log_area_size)?;

            pm_region.flush();

            proof {
                // TODO: refactor this into a lemma
                let bytes = pm_region@.committed();
                let recovered_view = Self::physical_recover(bytes, version_metadata, overall_metadata);
                lemma_establish_extract_bytes_equivalence(pre_log_setup_bytes, bytes);

                // First, prove that the recovered view is Some if recovery of all of the other components succeeds.
                // For most of these, we just need to prove that the log setup function didn't modify the corresponding bytes,
                // which is already part of log setup's postcondition, but we need to invoke lemma_subrange_of_extract_bytes_equal
                // to make Verus do the required reasoning about subranges.

                // Op log recovery succeeds
                let recovered_log = UntrustedOpLog::<K, L>::recover(bytes, version_metadata, overall_metadata);
                let recovered_log = recovered_log.unwrap();

                // At setup, we know that a logical log corresponding to the physical log exists, because the physical log is empty
                assert(exists |logical_log: Seq<LogicalOpLogEntry<L>>| 
                    Self::phys_log_corresponds_to_logical_log(bytes, recovered_log.physical_op_list, logical_log, version_metadata, overall_metadata)) 
                by {
                    assert(recovered_log.physical_op_list.len() == 0);
                    let witness = Seq::<LogicalOpLogEntry<L>>::empty();
                    assert(Self::phys_log_corresponds_to_logical_log(bytes, recovered_log.physical_op_list, witness, version_metadata, overall_metadata));
                }

                // Main table recovery succeeds
                let main_table_bytes = extract_bytes(bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let logical_log = choose |logical_log: Seq<LogicalOpLogEntry<L>>| 
                    Self::phys_log_corresponds_to_logical_log(bytes, recovered_log.physical_op_list, logical_log, version_metadata, overall_metadata);
                let post_install_main_table_bytes = MainTable::<K>::spec_replay_log_main_table(main_table_bytes, logical_log);
                let recovered_main_table = parse_main_table::<K>(post_install_main_table_bytes, overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.main_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.main_table_size as nat);

                // Item table recover succeeds
                let item_table_bytes = extract_bytes(bytes, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let valid_indices = recovered_main_table.unwrap().valid_item_indices();
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.item_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.item_table_size as nat);

                // List recover succeeds
                let list_area_bytes = extract_bytes(bytes, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                lemma_subrange_of_extract_bytes_equal(bytes, 0, overall_metadata.list_area_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.list_area_size as nat);
                
                assert(forall |i: int| 0 <= i < recovered_main_table.unwrap().get_durable_main_table().len() ==> #[trigger] recovered_main_table.unwrap().get_durable_main_table()[i] is None);

                DurableList::<K, L>::lemma_parse_each_list_succeeds_if_no_valid_metadata_entries(
                    recovered_main_table.unwrap().get_durable_main_table(),
                    list_area_bytes,
                    Map::empty(),
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node,
                );

                // Now need to prove that the recovered view matches init, i.e. that it results in an empty map.
                assert(recovered_view.unwrap().contents =~= Map::<int, DurableKvStoreViewEntry<K, I, L>>::empty());
            }

            Ok(())
        }


        fn start(
            mut wrpm_region: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            Tracked(perm): Tracked<&Perm>,
            Ghost(state): Ghost<DurableKvStoreView<K, I, L>>,
        ) -> (result: Result<Self, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                wrpm_region.inv(),
                wrpm_region@.no_outstanding_writes(),
                version_metadata == deserialize_version_metadata(wrpm_region@.committed()),
                overall_metadata == deserialize_overall_metadata(wrpm_region@.committed(),
                                                                 version_metadata.overall_metadata_addr),
                Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(state),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= wrpm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                forall |s| #[trigger] perm.check_permission(s) <==> Self::physical_recover(s, version_metadata, overall_metadata) == Some(state),
                wrpm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 < abstract_log.len() <= u64::MAX
                }),
                K::spec_size_of() > 0,
                // TODO: move these into one of the metadata validity spec fns
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size < overall_metadata.region_size,
                overall_metadata.item_size + u64::spec_size_of() <= u64::MAX,
            ensures
                match result {
                    // the primary postcondition is just that we've recovered to the target state, which 
                    // is required by the precondition to be the physical recovery view of the wrpm_region we passed in.
                    Ok(kvstore) => {
                        &&& kvstore@ == state
                        &&& kvstore.valid()
                        &&& kvstore.wrpm@.no_outstanding_writes()
                        &&& kvstore.constants() == wrpm_region.constants()
                        &&& kvstore.pending_allocations().is_empty()
                        &&& kvstore.pending_deallocations().is_empty()
                    }
                    Err(KvError::CRCMismatch) => !wrpm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                    Err(KvError::PmemErr { pmem_err }) => true,
                    Err(KvError::InternalError) => true,
                    Err(_) => true // TODO
                }
        {
            let ghost old_wrpm = wrpm_region;
            // 1. Start the log and obtain logged operations (if any)
            // We obtain physical log entries in an unparsed vector as parsing them would require an additional copy in DRAM
            let (mut op_log, phys_log) = UntrustedOpLog::<K, L>::start(&wrpm_region, version_metadata, overall_metadata)?;
            assert(op_log.inv(wrpm_region@, version_metadata, overall_metadata));

            // 2. Replay the log onto the entire PM region
            // Log entries are replayed blindly onto bytes; components do not have their own
            // replay functions. We only parse them after finishing log replay

            if phys_log.len() > 0 {
                proof { PhysicalOpLogEntry::lemma_abstract_log_inv_implies_concrete_log_inv(phys_log, version_metadata, overall_metadata); 
                }

                Self::install_log(&mut wrpm_region, version_metadata, overall_metadata, &phys_log, Tracked(perm));

                proof { 
                    op_log.lemma_same_bytes_preserve_op_log_invariant(old_wrpm, wrpm_region, version_metadata, overall_metadata);
                    assert(Self::apply_physical_log_entries(old_wrpm@.committed(), op_log@.physical_op_list).unwrap() == wrpm_region@.committed());
                    assert(Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(state));
                }

                assert({
                    &&& version_metadata == deserialize_version_metadata(wrpm_region@.committed())
                    &&& overall_metadata == deserialize_overall_metadata(wrpm_region@.committed(),
                                                                       version_metadata.overall_metadata_addr)
                });
                let ghost recovered_log = UntrustedOpLog::<K, L>::recover(old_wrpm@.committed(), version_metadata, overall_metadata).unwrap();
                let ghost physical_log_entries = recovered_log.physical_op_list;

                // We can now clear the log, since we have installed and flushed it.
                let ghost crash_pred = |s: Seq<u8>| { Self::physical_recover(s, version_metadata, overall_metadata) == Some(state) };
                proof {
                    assert(Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(state));
                    assert(wrpm_region@.can_crash_as(wrpm_region@.committed()));
                    assert(wrpm_region@.no_outstanding_writes());
                    lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(wrpm_region@);
                    assert(forall |s| wrpm_region@.can_crash_as(s) ==> s == wrpm_region@.committed());

                    Self::lemma_clear_log_is_crash_safe(wrpm_region, op_log, version_metadata,
                        overall_metadata, crash_pred, state, perm,);
            }

                let ghost pre_clear_wrpm = wrpm_region;
                op_log.clear_log(&mut wrpm_region, version_metadata, overall_metadata, Ghost(crash_pred), Tracked(perm))?;

                proof {
                    assert(states_differ_only_in_log_region(pre_clear_wrpm@.committed(), wrpm_region@.committed(), 
                        overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        pre_clear_wrpm@.committed(), wrpm_region@.committed(), version_metadata, overall_metadata);
                    assert(Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == Some(state));
                }
            } 
            
            // We can now start the rest of the components. 
            // We've already played the log, so we won't do any additional writes from this point on.
            // We use read-only subregions to make reasoning about each region separately easier

            let pm_region = wrpm_region.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.main_table_addr, Ghost(overall_metadata.main_table_size as nat));
            let item_table_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.item_table_addr, Ghost(overall_metadata.item_table_size as nat));
            let list_area_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.list_area_addr, Ghost(overall_metadata.list_area_size as nat));
            proof {
                // Prove that since we know overall recovery succeeded, parsing/starting the rest of the components will also succeed
                let mem = pm_region@.committed();
                let main_table_region = extract_bytes(mem, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let item_table_region = extract_bytes(mem, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let list_area_region = extract_bytes(mem, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                assert(main_table_region == main_table_subregion.view(pm_region).committed());
                assert(item_table_region == item_table_subregion.view(pm_region).committed());
                assert(list_area_region == list_area_subregion.view(pm_region).committed());

                lemma_physical_recover_succeeds_implies_component_parse_succeeds::<Perm, PM, K, I, L>(mem, version_metadata, overall_metadata);
            }
            
            // start each region
            let (main_table, entry_list) = MainTable::<K>::start::<PM, I, L>(&main_table_subregion, pm_region, overall_metadata, version_metadata)?;
            let item_table = DurableItemTable::<K, I>::start::<PM, L>(&item_table_subregion, pm_region, &entry_list, overall_metadata, version_metadata)?;
            let durable_list = DurableList::<K, L>::start::<PM, I>(&list_area_subregion, pm_region, &main_table, overall_metadata, version_metadata)?;

            let durable_kv_store = Self {
                version_metadata,
                overall_metadata,
                item_table,
                durable_list,
                log: op_log,
                main_table: main_table,
                wrpm: wrpm_region,
                pending_updates: Vec::new(),
            };

            // Prove that the pending allocations invariant holds here after setting up
            // all components
            assert(durable_kv_store.pending_alloc_inv()) by {
                let durable_state_bytes = wrpm_region@.committed();
                let tentative_state_bytes = Self::apply_physical_log_entries(wrpm_region@.flush().committed(),
                    durable_kv_store.log@.commit_op_log().physical_op_list).unwrap();
                assert(durable_state_bytes == tentative_state_bytes);

                let durable_main_table_region = extract_bytes(durable_state_bytes, durable_kv_store.overall_metadata.main_table_addr as nat, 
                    durable_kv_store.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_region, durable_kv_store.overall_metadata.num_keys,
                    durable_kv_store.overall_metadata.main_table_entry_size).unwrap();

                assert(durable_main_table_region == main_table_subregion.view(pm_region).committed());
                assert(durable_main_table_view == durable_kv_store.main_table@);

                assert(durable_kv_store.main_table.pending_alloc_inv(main_table_subregion.view(pm_region).committed(),
                    main_table_subregion.view(pm_region).committed(), overall_metadata));
                assert(durable_kv_store.main_table.pending_alloc_inv(durable_main_table_region,
                    durable_main_table_region, overall_metadata));
                assert(durable_kv_store.item_table.pending_alloc_inv(
                    main_table@.valid_item_indices(),
                    main_table@.valid_item_indices(),
                    main_table@.valid_item_indices(),
                ));
            }

            proof {
                let recovered_log = UntrustedOpLog::<K, L>::recover(old_wrpm@.committed(), version_metadata, overall_metadata).unwrap();
                let physical_log_entries = recovered_log.physical_op_list;
                assert(states_differ_only_in_log_region(
                    DurableKvStore::<Perm, PM, K, I, L>::apply_physical_log_entries(old_wrpm@.committed(), physical_log_entries).unwrap(),
                    wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                );

                // each recovered component parses correctly
                assert(parse_main_table::<K>(main_table_subregion.view(pm_region).committed(), overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap() == main_table@);
                assert(parse_item_table::<I, K>(item_table_subregion.view(pm_region).committed(), overall_metadata.num_keys as nat, main_table@.valid_item_indices()).unwrap() == item_table@);
                assert(DurableList::<K, L>::parse_all_lists(main_table@, list_area_subregion.view(pm_region).committed(), overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node).unwrap() == durable_list@);

                assert(durable_kv_store@ == Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata).unwrap());
                assert(durable_kv_store@ == Self::recover_from_component_views(main_table@, item_table@, durable_list@));
                assert(PhysicalOpLogEntry::vec_view(durable_kv_store.pending_updates) == durable_kv_store.log@.physical_op_list);
            }

            /*
            // TODO - Prove that the physical and logical recovery states match.
            let ghost physical_recovery_state = Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata);
            let ghost logical_recovery_state = Self::logical_recover(wrpm_region@.committed(), version_metadata, overall_metadata);
            assert(physical_recovery_state == logical_recovery_state);
            */

            proof {
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
                    durable_kv_store.wrpm@);
                durable_kv_store.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
            }
            
            Ok(durable_kv_store)
        }

        // This function installs the log by blindly replaying physical log entries onto the WRPM region. All writes
        // made by this function are crash-safe; if we crash during this operation, replaying the full log on the resulting
        // crash state gets us to the final desired state. This function does not return a Result because it cannot fail
        // as long as the log is well-formed, which is required by the precondition.
        fn install_log(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            phys_log: &Vec<PhysicalOpLogEntry>,
            Tracked(perm): Tracked<&Perm>,
        ) 
            where 
                PM: PersistentMemoryRegion,
                Perm: CheckPermission<Seq<u8>>,
            requires
                old(wrpm_region).inv(),
                old(wrpm_region)@.no_outstanding_writes(),
                old(wrpm_region)@.len() == overall_metadata.region_size,
                PhysicalOpLogEntry::log_inv(*phys_log, version_metadata, overall_metadata),
                phys_log.len() > 0,
                UntrustedLogImpl::recover(old(wrpm_region)@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) is Some,
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(old(wrpm_region)@.committed(), version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                forall |s| Self::physical_recover(old(wrpm_region)@.committed(), version_metadata, overall_metadata) == Self::physical_recover(s, version_metadata, overall_metadata) 
                    ==> perm.check_permission(s),
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                Self::physical_recover(old(wrpm_region)@.committed(), version_metadata, overall_metadata) is Some,
            ensures 
                wrpm_region.inv(),
                wrpm_region@.no_outstanding_writes(),
                wrpm_region@.len() == overall_metadata.region_size,
                wrpm_region.constants() == old(wrpm_region).constants(),
                ({
                    let true_recovery_state = Self::physical_recover(old(wrpm_region)@.committed(), version_metadata, overall_metadata).unwrap();
                    let recovery_state = Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata);
                    &&& recovery_state matches Some(recovery_state)
                    &&& recovery_state == true_recovery_state
                }),
                ({
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let true_final_state = Self::apply_physical_log_entries(old(wrpm_region)@.committed(), phys_log_view);
                    wrpm_region@.committed() == true_final_state.unwrap()
                }),
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(wrpm_region@.committed(), version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                extract_bytes(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
                    extract_bytes(old(wrpm_region)@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
                extract_bytes(wrpm_region@.committed(), 0, VersionMetadata::spec_size_of()) == 
                    extract_bytes(old(wrpm_region)@.committed(), 0, VersionMetadata::spec_size_of()),
                extract_bytes(wrpm_region@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()) == 
                    extract_bytes(old(wrpm_region)@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()),    
        {
            let log_start_addr = overall_metadata.log_area_addr;
            let log_size = overall_metadata.log_area_size;
            let region_size = overall_metadata.region_size;

            let ghost old_phys_log = phys_log;
            let ghost old_wrpm = wrpm_region@.committed();
            let ghost old_wrpm_constants = wrpm_region.constants();

            let ghost final_recovery_state = Self::physical_recover(old(wrpm_region)@.committed(), version_metadata, overall_metadata).unwrap();

            let mut index = 0;

            proof {
                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                let replayed_ops = phys_log_view.subrange(0, index as int);
                let remaining_ops = phys_log_view.subrange(index as int, phys_log.len() as int);
                let final_mem = Self::apply_physical_log_entries(old_wrpm, phys_log_view).unwrap();
                let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops).unwrap();

                assert(replayed_ops.len() == 0);
                assert(remaining_ops == phys_log_view);
                assert(current_mem == old_wrpm);
                assert(Self::apply_physical_log_entries(old_wrpm, remaining_ops).unwrap() == final_mem);
            }

            while index < phys_log.len() 
                invariant
                    old_wrpm.len() == wrpm_region@.len(),
                    PhysicalOpLogEntry::log_inv(*phys_log, version_metadata, overall_metadata),
                    forall |s| Self::physical_recover(s, version_metadata, overall_metadata) == 
                        Some(final_recovery_state) ==> #[trigger] perm.check_permission(s),
                    Self::physical_recover(wrpm_region@.committed(), version_metadata, overall_metadata) == 
                        Some(final_recovery_state),
                    old_phys_log == phys_log,
                    ({
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        let replayed_ops = phys_log_view.subrange(0, index as int);
                        let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops);
                        &&& current_mem is Some 
                        &&& current_mem.unwrap() == wrpm_region@.committed()
                        &&& recovery_write_region_invariant::<Perm, PM, K, I, L>(*wrpm_region, version_metadata, overall_metadata, phys_log_view)
                    }),
                    0 <= index <= phys_log.len(),
                    old_wrpm_constants == wrpm_region.constants(),
                    extract_bytes(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
                        extract_bytes(old_wrpm, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat),
                    extract_bytes(wrpm_region@.committed(), 0, VersionMetadata::spec_size_of()) == 
                        extract_bytes(old(wrpm_region)@.committed(), 0, VersionMetadata::spec_size_of()),
                    extract_bytes(wrpm_region@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()) == 
                        extract_bytes(old(wrpm_region)@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()),    
                    VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
            {
                let op = &phys_log[index];

                proof {
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);

                    // These two assertions are obvious from the loop invariant, but we need them to for triggers
                    assert(op.inv(version_metadata, overall_metadata)); 
                    assert({
                        ||| op.absolute_addr + op.len <= overall_metadata.log_area_addr
                        ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= op.absolute_addr
                    });

                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    assert(phys_log_view[index as int] == phys_log[index as int]@);
                    assert(forall |i: int| op.absolute_addr <= i < op.absolute_addr + op.len ==> 
                        #[trigger] addr_modified_by_recovery(phys_log_view, i));

                    // Prove that any write to an address modified by recovery is crash-safe
                    lemma_safe_recovery_writes::<Perm, PM, K, I, L>(*wrpm_region, version_metadata, overall_metadata, phys_log_view, op.absolute_addr as int, op.bytes@);
                }

                proof {
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let replayed_ops = phys_log_view.subrange(0, index as int);
                    let current_mem = Self::apply_physical_log_entries(old_wrpm, replayed_ops);

                    // From the loop invariant
                    assert(current_mem is Some);
                    assert(current_mem.unwrap() == wrpm_region@.committed());

                    let new_wrpm = wrpm_region@.write(op.absolute_addr as int, op.bytes@).flush();
                    let new_replayed_ops = phys_log_view.subrange(0, index + 1);
                    let new_mem = Self::apply_physical_log_entries(old_wrpm, new_replayed_ops);

                    Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(old_wrpm, version_metadata, overall_metadata, new_replayed_ops);
                    assert(new_mem is Some);

                    let step_mem = Self::apply_physical_log_entry(current_mem.unwrap(), op@);

                    assert(step_mem is Some);
                    assert(new_replayed_ops == replayed_ops + seq![op@]);

                    assert(Self::apply_physical_log_entries(old_wrpm, replayed_ops) is Some);
                    assert(replayed_ops == new_replayed_ops.subrange(0, new_replayed_ops.len() - 1));

                    assert(step_mem.unwrap() == new_wrpm.committed());
                    assert(step_mem.unwrap() == new_mem.unwrap());

                    assert(new_mem.unwrap() == new_wrpm.committed());
                }

                let ghost pre_write_wrpm = wrpm_region@;

                // write the current op's updates to the specified location on storage
                wrpm_region.write(op.absolute_addr, op.bytes.as_slice(), Tracked(perm));
                wrpm_region.flush();

                assert(extract_bytes(wrpm_region@.committed(), overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat) == 
                    extract_bytes(old_wrpm, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                assert(extract_bytes(wrpm_region@.committed(), 0, VersionMetadata::spec_size_of()) == 
                    extract_bytes(old(wrpm_region)@.committed(), 0, VersionMetadata::spec_size_of()));
                assert(extract_bytes(wrpm_region@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()) == 
                    extract_bytes(old(wrpm_region)@.committed(), version_metadata.overall_metadata_addr as nat, OverallMetadata::spec_size_of()));

                index += 1;
            }

            proof {
                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                assert(phys_log_view.subrange(0, index as int) == phys_log_view);
            }
        }

        // This function takes an offset into the main table, looks up the corresponding item,
        // and returns it if it exists.
        pub fn read_item(
            &self,
            metadata_index: u64
        ) -> (result: Result<Box<I>, KvError<K>>)
            requires
                self.valid(),
                self@.contains_key(metadata_index as int),
            ensures
                match result {
                    Ok(item) => {
                        match self@[metadata_index as int] {
                            Some(entry) => entry.item() == item,
                            None => false,
                        }
                    },
                    Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption,
                    Err(_) => false,
                }
        {
            assert(metadata_index < self.overall_metadata.num_keys);

            let pm = self.wrpm.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(
                pm,
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );
            let (key, metadata) = match self.main_table.get_key_and_metadata_entry_at_index(
                &main_table_subregion,
                pm,
                metadata_index,
                Ghost(self.overall_metadata),
            ) {
                Ok((key, metadata)) => (key, metadata),
                Err(e) => { assert(e is CRCMismatch); return Err(e); },
            };

            let item_table_index = metadata.item_index;
            let item_table_subregion = PersistentMemorySubregion::new(
                pm,
                self.overall_metadata.item_table_addr,
                Ghost(self.overall_metadata.item_table_size as nat));
            self.item_table.read_item(
                &item_table_subregion,
                pm,
                item_table_index,
                Ghost(self.overall_metadata),
                Ghost(self.main_table@.valid_item_indices()),
            )
        }

        spec fn get_writable_mask_for_main_table(self) -> (mask: spec_fn(int) -> bool)
        {
            let main_table_addr = self.overall_metadata.main_table_addr as int;
            let main_table_size = self.overall_metadata.main_table_size as int;
            let main_table_entry_size = self.overall_metadata.main_table_entry_size;
            |addr: int| {
                let relative_addr = addr - main_table_addr;
                let which_entry = relative_addr / main_table_entry_size as int;
                let entry_offset = index_to_offset(which_entry as nat, main_table_entry_size as nat);
                &&& 0 <= relative_addr < main_table_size
                &&& 0 <= which_entry < self.overall_metadata.num_keys
                &&& entry_offset + u64::spec_size_of() <= relative_addr < entry_offset + main_table_entry_size
                &&& self.main_table.allocator_view().contains(which_entry as u64)
            }
        }

        closed spec fn condition_preserved_by_subregion_masks(self) -> (spec_fn(Seq<u8>) -> bool)
        {
            let version_metadata = self.version_metadata;
            let overall_metadata = self.overall_metadata;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            |s: Seq<u8>| {
                &&& UntrustedOpLog::<K, L>::recover(s, version_metadata, overall_metadata) ==
                      Some(AbstractOpLogState::initialize())
                &&& parse_main_table::<K>(extract_bytes(s, main_table_addr as nat, main_table_size as nat),
                                             num_keys, main_table_entry_size) ==
                      Some(self.main_table@)
                &&& parse_item_table::<I, K>(extract_bytes(s, item_table_addr as nat, item_table_size as nat),
                                            num_keys as nat, self.main_table@.valid_item_indices()) ==
                      Some(self.item_table@)
                &&& Self::physical_recover(s, version_metadata, overall_metadata) == Some(self@)
            }
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_by_crashing(self)
            requires
                self.inv(),
                !self.log@.op_list_committed,
            ensures
                forall|s| self.wrpm@.can_crash_as(s) ==> self.condition_preserved_by_subregion_masks()(s)
        {
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;

            let condition = self.condition_preserved_by_subregion_masks();
            assert forall|s| self.wrpm@.can_crash_as(s) implies condition(s) by {
                let recovered_log = UntrustedOpLog::<K, L>::recover(s, self.version_metadata,
                                                                    overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, overall_metadata);
                assert(Self::apply_physical_log_entries(s, recovered_log.unwrap().physical_op_list) == Some(s));
                lemma_subregion_view_can_crash_as_subrange(self.wrpm@, s, main_table_addr as nat, main_table_size as nat);
                lemma_subregion_view_can_crash_as_subrange(self.wrpm@, s, item_table_addr as nat, item_table_size as nat);
            }
        }

        proof fn lemma_writable_mask_for_main_table_suitable_for_creating_subregion(self, perm: &Perm)
            requires
                self.inv(),
                !self.log@.op_list_committed,
                forall|s| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                    #[trigger] perm.check_permission(s),
            ensures
                condition_sufficient_to_create_wrpm_subregion(
                    self.wrpm@, perm, self.overall_metadata.main_table_addr,
                                                                self.overall_metadata.main_table_size as nat,
                    self.get_writable_mask_for_main_table(),
                    self.condition_preserved_by_subregion_masks(),
                )
        {
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let list_area_addr = overall_metadata.list_area_addr;
            let list_area_size = overall_metadata.list_area_size;
            let log_area_addr = overall_metadata.log_area_addr;
            let log_area_size = overall_metadata.log_area_size;

            let condition = self.condition_preserved_by_subregion_masks();
            self.lemma_condition_preserved_by_subregion_masks_preserved_by_crashing();
            assert forall|s1: Seq<u8>, s2: Seq<u8>| {
                       &&& condition(s1)
                       &&& s1.len() == s2.len() == self.wrpm@.len()
                       &&& memories_differ_only_where_subregion_allows(s1, s2, main_table_addr as nat,
                                                                      main_table_size as nat,
                                                                      self.get_writable_mask_for_main_table())
                    } implies condition(s2) by {
                let ss1 = extract_bytes(s1, main_table_addr as nat, main_table_size as nat);
                let ss2 = extract_bytes(s2, main_table_addr as nat, main_table_size as nat);
                assert forall|addr: int| 0 <= addr < ss1.len() && ss1[addr] != #[trigger] ss2[addr] implies
                           address_belongs_to_invalid_main_table_entry(addr, ss1, num_keys, main_table_entry_size) by {
                    assert(self.get_writable_mask_for_main_table()(addr + main_table_addr));
                    let which_entry = addr / main_table_entry_size as int;
                    lemma_valid_entry_index(which_entry as nat, num_keys as nat, main_table_entry_size as nat);
                    assert(self.main_table.allocator_view().contains(which_entry as u64));
                    assert(self.main_table.free_indices().contains(which_entry as u64));
                    assert(self.main_table@.durable_main_table[which_entry as int] is None);
                    let entry_bytes = extract_bytes(ss1,
                                                    index_to_offset(which_entry as nat, main_table_entry_size as nat),
                                                    main_table_entry_size as nat);
                    assert(validate_main_entry::<K>(entry_bytes, num_keys as nat));
                    assert(parse_main_entry::<K>(entry_bytes, num_keys as nat) is None);
                    let cdb_bytes = extract_bytes(ss1,
                                                  index_to_offset(which_entry as nat, main_table_entry_size as nat),
                                                  u64::spec_size_of());
                    assert(cdb_bytes =~= extract_bytes(entry_bytes, 0, u64::spec_size_of()));
                }
                lemma_parse_main_table_doesnt_depend_on_fields_of_invalid_entries::<K>(
                    ss1, ss2, num_keys, main_table_entry_size
                );
                assert(UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata) ==
                       UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, overall_metadata))
                    by {
                    assert(extract_bytes(s1, log_area_addr as nat, log_area_size as nat) =~=
                           extract_bytes(s2, log_area_addr as nat, log_area_size as nat));
                    lemma_same_log_bytes_recover_to_same_state(s1, s2, log_area_addr as nat, log_area_size as nat,
                                                               s1.len());
                }
                let recovered_log = UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, overall_metadata);
                assert(parse_main_table::<K>(extract_bytes(s2, main_table_addr as nat, main_table_size as nat),
                                                 num_keys, main_table_entry_size) ==
                       Some(self.main_table@));
                assert(Self::apply_physical_log_entries(s2, recovered_log.unwrap().physical_op_list) == Some(s2));
                assert(extract_bytes(s1, item_table_addr as nat, item_table_size as nat) =~=
                       extract_bytes(s2, item_table_addr as nat, item_table_size as nat));
                assert(parse_item_table::<I, K>(extract_bytes(s2, item_table_addr as nat, item_table_size as nat),
                                            num_keys as nat, self.main_table@.valid_item_indices()) ==
                      Some(self.item_table@));
                assert(extract_bytes(s1, list_area_addr as nat, list_area_size as nat) =~=
                       extract_bytes(s2, list_area_addr as nat, list_area_size as nat));
                assert(Self::physical_recover(s2, self.version_metadata, overall_metadata) == Some(self@));
            }
        }

        spec fn main_table_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                               self.overall_metadata.main_table_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat)
        }

        spec fn item_table_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                               self.overall_metadata.item_table_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                   self.overall_metadata.item_table_size as nat)
        }

        spec fn log_area_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.wrpm@, self.overall_metadata.log_area_addr as nat,
                               self.overall_metadata.log_area_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.log_area_addr as nat,
                                   self.overall_metadata.log_area_size as nat)
        }

        spec fn list_area_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                               self.overall_metadata.list_area_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.list_area_addr as nat,
                                   self.overall_metadata.list_area_size as nat)
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
            self,
            old_self: Self,
            subregion: WriteRestrictedPersistentMemorySubregion,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.log@.op_list_committed,
                condition_sufficient_to_create_wrpm_subregion(
                    old_self.wrpm@, perm, old_self.overall_metadata.main_table_addr,
                    old_self.overall_metadata.main_table_size as nat,
                    old_self.get_writable_mask_for_main_table(),
                    old_self.condition_preserved_by_subregion_masks(),
                ),
                subregion.constants() == old_self.wrpm.constants(),
                subregion.start() == old_self.overall_metadata.main_table_addr,
                subregion.len() == old_self.overall_metadata.main_table_size,
                subregion.initial_region_view() == old_self.wrpm@,
                subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_main_table(),
                subregion.inv(&self.wrpm, perm),
                self == (Self{ wrpm: self.wrpm, main_table: self.main_table, ..old_self }),
            ensures
                self.wrpm.inv(),
                self.wrpm.constants() == old_self.wrpm.constants(),
                self.wrpm@.len() == subregion.initial_region_view().len(),
                views_differ_only_where_subregion_allows(subregion.initial_region_view(), self.wrpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat,
                                                         old_self.get_writable_mask_for_main_table()),
                self.item_table_view_matches(old_self.wrpm@),
                self.list_area_view_matches(old_self.wrpm@),
                self.log_area_view_matches(old_self.wrpm@),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    &&& forall|s| self.wrpm@.can_crash_as(s) ==> condition(s)
                    &&& condition(self.wrpm@.committed())
                })
        {
            subregion.lemma_reveal_opaque_inv(&self.wrpm);

            let condition = old_self.condition_preserved_by_subregion_masks();
            assert forall|s| self.wrpm@.can_crash_as(s) implies condition(s) by {
                let s_old = lemma_get_crash_state_given_one_for_other_view_differing_only_where_subregion_allows(
                    self.wrpm@,
                    old_self.wrpm@,
                    s,
                    old_self.overall_metadata.main_table_addr as nat,
                    old_self.overall_metadata.main_table_size as nat,
                    old_self.get_writable_mask_for_main_table()
                );
                assert(condition(s_old));
                assert(s_old.len() == s.len() == old_self.wrpm@.len());
                assert(memories_differ_only_where_subregion_allows(
                    s_old, s,
                    old_self.overall_metadata.main_table_addr as nat,
                    old_self.overall_metadata.main_table_size as nat,
                    old_self.get_writable_mask_for_main_table()
                ));
            }

            lemma_persistent_memory_view_can_crash_as_committed(self.wrpm@);

            assert(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat));
            assert(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat));
            assert(get_subregion_view(self.wrpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat));
        }

        proof fn lemma_main_table_subregion_grants_access_to_free_slots(
            self,
            subregion: WriteRestrictedPersistentMemorySubregion,
        )
            requires
                self.inv(),
                subregion.start() == self.overall_metadata.main_table_addr,
                subregion.len() == self.overall_metadata.main_table_size,
                subregion.is_writable_absolute_addr_fn() == self.get_writable_mask_for_main_table(),
            ensures
                self.main_table.subregion_grants_access_to_free_slots(subregion),

        {

            assert forall|idx: u64| {
                &&& idx < self.main_table@.len()
                &&& self.main_table.allocator_view().contains(idx)
            } implies #[trigger] subregion_grants_access_to_main_table_entry::<K>(subregion, idx) by {
                let entry_size = self.overall_metadata.main_table_entry_size;
                assert forall|addr: u64| idx * entry_size + u64::spec_size_of() <= addr
                           < idx * entry_size + entry_size implies
                           subregion.is_writable_relative_addr(addr as int) by {
                    lemma_valid_entry_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size as nat);
                    lemma_addr_in_entry_divided_by_entry_size(idx as nat, entry_size as nat, addr as int);
                    assert(self.get_writable_mask_for_main_table()(addr + self.overall_metadata.main_table_addr));
            }
        }
        }

        spec fn get_writable_mask_for_item_table(self) -> (mask: spec_fn(int) -> bool)
        {
            |addr: int| address_belongs_to_invalid_item_table_entry::<I>(addr - self.overall_metadata.item_table_addr,
                                                                       self.overall_metadata.num_keys,
                                                                       self.main_table@.valid_item_indices())
        }

        proof fn lemma_writable_mask_for_item_table_suitable_for_creating_subregion(
            self,
            perm: &Perm
        )
            requires
                self.inv(),
                !self.log@.op_list_committed,
                forall|s| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                    #[trigger] perm.check_permission(s),
            ensures
                condition_sufficient_to_create_wrpm_subregion(
                    self.wrpm@, perm, self.overall_metadata.item_table_addr,
                    self.overall_metadata.item_table_size as nat,
                    self.get_writable_mask_for_item_table(),
                    self.condition_preserved_by_subregion_masks(),
                )
        {
            let item_entry_size = I::spec_size_of() + u64::spec_size_of();
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let list_area_addr = overall_metadata.list_area_addr;
            let list_area_size = overall_metadata.list_area_size;
            let log_area_addr = overall_metadata.log_area_addr;
            let log_area_size = overall_metadata.log_area_size;

            let condition = self.condition_preserved_by_subregion_masks();
            self.lemma_condition_preserved_by_subregion_masks_preserved_by_crashing();
            assert forall|s1: Seq<u8>, s2: Seq<u8>| {
                       &&& condition(s1)
                       &&& s1.len() == s2.len() == self.wrpm@.len()
                       &&& memories_differ_only_where_subregion_allows(s1, s2, item_table_addr as nat,
                                                                      item_table_size as nat,
                                                                      self.get_writable_mask_for_item_table())
                    } implies condition(s2) by {
                let ss1 = extract_bytes(s1, item_table_addr as nat, item_table_size as nat);
                let ss2 = extract_bytes(s2, item_table_addr as nat, item_table_size as nat);
                assert forall|addr: int| 0 <= addr < ss2.len() && ss1[addr] != #[trigger] ss2[addr] implies
                           address_belongs_to_invalid_item_table_entry::<I>(
                               addr, num_keys, self.main_table@.valid_item_indices()
                           ) by {
                }
                lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                    ss1, ss2, num_keys,
                    self.main_table@.valid_item_indices()
                );
                assert(UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata) ==
                       UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, overall_metadata))
                    by {
                    assert(extract_bytes(s1, log_area_addr as nat, log_area_size as nat) =~=
                           extract_bytes(s2, log_area_addr as nat, log_area_size as nat));
                    lemma_same_log_bytes_recover_to_same_state(s1, s2, log_area_addr as nat, log_area_size as nat,
                                                               s1.len());
                }
                let recovered_log = UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, overall_metadata);
                assert(Self::apply_physical_log_entries(s2, recovered_log.unwrap().physical_op_list) == Some(s2));
                assert(extract_bytes(s1, main_table_addr as nat, main_table_size as nat) =~=
                       extract_bytes(s2, main_table_addr as nat, main_table_size as nat));
                assert(parse_main_table::<K>(extract_bytes(s2, main_table_addr as nat, main_table_size as nat),
                                                 num_keys, main_table_entry_size) ==
                       Some(self.main_table@));
                assert(parse_item_table::<I, K>(extract_bytes(s2, item_table_addr as nat, item_table_size as nat),
                                            num_keys as nat, self.main_table@.valid_item_indices()) ==
                      Some(self.item_table@));
                assert(extract_bytes(s1, list_area_addr as nat, list_area_size as nat) =~=
                       extract_bytes(s2, list_area_addr as nat, list_area_size as nat));
                assert(Self::physical_recover(s2, self.version_metadata, overall_metadata) == Some(self@));
            }
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
            self,
            old_self: Self,
            subregion: WriteRestrictedPersistentMemorySubregion,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.log@.op_list_committed,
                condition_sufficient_to_create_wrpm_subregion(
                    old_self.wrpm@, perm, old_self.overall_metadata.item_table_addr,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table(),
                    old_self.condition_preserved_by_subregion_masks(),
                ),
                subregion.constants() == old_self.wrpm.constants(),
                subregion.start() == old_self.overall_metadata.item_table_addr,
                subregion.len() == old_self.overall_metadata.item_table_size,
                subregion.initial_region_view() == old_self.wrpm@,
                subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_item_table(),
                subregion.inv(&self.wrpm, perm),
                self == (Self{ wrpm: self.wrpm, item_table: self.item_table, ..old_self }),
            ensures
                self.wrpm.inv(),
                self.wrpm.constants() == old_self.wrpm.constants(),
                self.wrpm@.len() == subregion.initial_region_view().len(),
                views_differ_only_where_subregion_allows(subregion.initial_region_view(), self.wrpm@,
                                                         self.overall_metadata.item_table_addr as nat,
                                                         self.overall_metadata.item_table_size as nat,
                                                         old_self.get_writable_mask_for_item_table()),
                self.main_table_view_matches(old_self.wrpm@),
                self.list_area_view_matches(old_self.wrpm@),
                self.log_area_view_matches(old_self.wrpm@),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    &&& forall|s| self.wrpm@.can_crash_as(s) ==> condition(s)
                    &&& condition(self.wrpm@.committed())
                })
        {
            subregion.lemma_reveal_opaque_inv(&self.wrpm);

            let condition = old_self.condition_preserved_by_subregion_masks();
            assert forall|s| self.wrpm@.can_crash_as(s) implies condition(s) by {
                let s_old = lemma_get_crash_state_given_one_for_other_view_differing_only_where_subregion_allows(
                    self.wrpm@,
                    old_self.wrpm@,
                    s,
                    old_self.overall_metadata.item_table_addr as nat,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table()
                );
                assert(condition(s_old));
                assert(s_old.len() == s.len() == old_self.wrpm@.len());
                assert(memories_differ_only_where_subregion_allows(
                    s_old, s,
                    old_self.overall_metadata.item_table_addr as nat,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table()
                ));
            }

            lemma_persistent_memory_view_can_crash_as_committed(self.wrpm@);

            assert(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat));
            assert(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat));
            assert(get_subregion_view(self.wrpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat) =~=
                   get_subregion_view(old_self.wrpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat));
        }

        proof fn lemma_reestablish_inv_after_tentatively_write_item(
            self,
            old_self: Self,
            item_index: u64,
            item: I,
        )
            requires
                old_self.inv(),
                !old_self.transaction_committed(),
                self == (Self { item_table: self.item_table, wrpm: self.wrpm, ..old_self }),
                self.wrpm.inv(),
                self.wrpm.constants() == old_self.wrpm.constants(),
                views_differ_only_where_subregion_allows(old_self.wrpm@, self.wrpm@,
                                                         self.overall_metadata.item_table_addr as nat,
                                                         self.overall_metadata.item_table_size as nat,
                                                         old_self.get_writable_mask_for_item_table()),
                self.main_table_view_matches(old_self.wrpm@),
                self.list_area_view_matches(old_self.wrpm@),
                self.log_area_view_matches(old_self.wrpm@),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    &&& forall|s| self.wrpm@.can_crash_as(s) ==> condition(s)
                    &&& condition(self.wrpm@.committed())
                }),
                self.item_table.inv(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata, self.main_table@.valid_item_indices()),
                old_self.item_table.allocator_view().contains(item_index),
                self.item_table@.durable_item_table == old_self.item_table@.durable_item_table,
                forall |i: int| 0 <= i < self.overall_metadata.num_keys && i != item_index ==>
                    #[trigger] self.item_table.outstanding_item_table@[i] ==
                               old_self.item_table.outstanding_item_table@[i],
                self.item_table.outstanding_item_table@[item_index as int] == Some(item),
                forall |other_index: u64| self.item_table.allocator_view().contains(other_index) <==>
                    old_self.item_table.allocator_view().contains(other_index) && other_index != item_index,
            ensures
                self.inv(),
                self.constants() == old_self.constants(),
                !self.transaction_committed(),
                forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==>
                    self.wrpm@.state[addr] == old_self.wrpm@.state[addr],
                forall|addr: int| self.version_metadata.overall_metadata_addr <= addr
                            < self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                    self.wrpm@.state[addr] == old_self.wrpm@.state[addr],
                self.main_table_view_matches(old_self.wrpm@),
                self.list_area_view_matches(old_self.wrpm@),
                self.log_area_view_matches(old_self.wrpm@),
        {
            assert(self.log.inv(self.wrpm@, self.version_metadata, self.overall_metadata)) by {
                assert(0 <= self.overall_metadata.log_area_addr < 
                    self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size <= 
                    self.overall_metadata.region_size);
                assert(0 < spec_log_header_area_size() <= spec_log_area_pos() < self.overall_metadata.log_area_size);
                self.log.lemma_same_op_log_view_preserves_invariant(old_self.wrpm, self.wrpm, 
                    self.version_metadata, self.overall_metadata);
            }
            lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                old_self.wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
            );
            self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
        }

        // This lemma proves that after abort, indices that were pending allocation prior to the abort
        // are invalid in the durable state. Note that this lemma should usually be called on the 
        // *pre-abort* self, not self after we've aborted the transaction in the op log, because
        // this lemma needs to see the pre-abort tentative state.
        proof fn lemma_metadata_pending_allocs_are_invalid_at_abort(self)
            requires 
                self.wrpm@.len() >= self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size,
                !self.transaction_committed(),
                forall |idx: u64| self.main_table.pending_allocations_view().contains(idx) ==>
                    idx < self.overall_metadata.num_keys,
                ({
                    let durable_main_table_subregion_view = get_subregion_view(self.wrpm@, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let durable_main_table_subregion_state = extract_bytes(self.wrpm@.committed(), 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let tentative_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                        self.log@.physical_op_list).unwrap();
                    let tentative_main_table_subregion_state = extract_bytes(tentative_bytes, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    &&& self.main_table.pending_alloc_inv(durable_main_table_subregion_state, 
                            tentative_main_table_subregion_state, self.overall_metadata)
                    &&& forall |s| #[trigger] durable_main_table_subregion_view.can_crash_as(s) ==> 
                            Some(self.main_table@) == parse_main_table::<K>(s, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size)
                })
            ensures 
                forall |idx: u64| #[trigger] self.main_table.pending_allocations_view().contains(idx) ==> {
                    self.main_table@.durable_main_table[idx as int] is None
                }
        {
            let durable_main_table_subregion_view = get_subregion_view(self.wrpm@, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let durable_main_table_subregion_state = extract_bytes(self.wrpm@.committed(), 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let durable_main_table_view = parse_main_table::<K>(durable_main_table_subregion_state,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            
            assert(durable_main_table_subregion_view.can_crash_as(durable_main_table_subregion_view.committed()));
            assert(durable_main_table_subregion_view.committed() == durable_main_table_subregion_state);
            assert(forall |s| #[trigger] durable_main_table_subregion_view.can_crash_as(s) ==> 
                Some(self.main_table@) == parse_main_table::<K>(s, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size));
            assert(durable_main_table_view == self.main_table@);

            let tentative_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.physical_op_list).unwrap();
            let tentative_main_table_subregion_state = extract_bytes(tentative_bytes, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_subregion_state,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

            assert(self.main_table.pending_alloc_inv(durable_main_table_subregion_state, 
                tentative_main_table_subregion_state, self.overall_metadata));

            assert forall |idx: u64| #[trigger] self.main_table.pending_allocations_view().contains(idx) implies {
                durable_main_table_view.durable_main_table[idx as int] is None
            } by {
                assert(self.main_table.pending_alloc_check(idx, durable_main_table_view, 
                    tentative_main_table_view));
            }
        }

        fn abort_after_failed_item_table_tentatively_write_item(
            &mut self,
            Ghost(pre_self): Ghost<Self>,
            Tracked(perm): Tracked<&Perm>
        )
            requires
                pre_self.inv(),
                !pre_self.transaction_committed(),
                pre_self.pending_alloc_inv(),
                old(self) == (Self { item_table: old(self).item_table, wrpm: old(self).wrpm, ..pre_self }),
                old(self).item_table_view_matches(pre_self.wrpm@),
                old(self).list_area_view_matches(pre_self.wrpm@),
                old(self).log_area_view_matches(pre_self.wrpm@),
                ({
                    let condition = pre_self.condition_preserved_by_subregion_masks();
                    &&& forall|s| old(self).wrpm@.can_crash_as(s) ==> condition(s)
                    &&& condition(old(self).wrpm@.committed())
                }),
                old(self).item_table.inv(
                    get_subregion_view(old(self).wrpm@, old(self).overall_metadata.item_table_addr as nat,
                                       old(self).overall_metadata.item_table_size as nat),
                    old(self).overall_metadata,
                    old(self).main_table@.valid_item_indices()
                ),
                old(self).item_table@ == pre_self.item_table@,
                old(self).item_table.outstanding_item_table@ == pre_self.item_table.outstanding_item_table@,
                old(self).item_table.allocator_view() == pre_self.item_table.allocator_view(),
                old(self).item_table.pending_allocations_view() == pre_self.item_table.pending_allocations_view(),
                old(self).item_table.allocator_view().len() == 0,
                old(self).wrpm == pre_self.wrpm,
                old(self).item_table@ == pre_self.item_table@,
                old(self).main_table == pre_self.main_table,
                ({
                    let main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(),
                        old(self).overall_metadata.main_table_addr as nat,
                        old(self).overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(main_table_subregion_view.committed(), old(self).overall_metadata.num_keys, 
                        old(self).overall_metadata.main_table_entry_size) is Some
                }),
            ensures
                self.inv(),
                self@ == pre_self@,
                self.constants() == pre_self.constants(),
                self.tentative_view() ==
                    Self::physical_recover_given_log(self.wrpm_view().flush().committed(),
                                                     self.spec_overall_metadata(), AbstractOpLogState::initialize()),
                !self.transaction_committed(),
                self.pending_allocations().is_empty(),
                self.pending_deallocations().is_empty(),
        {
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata,
                                                        self.overall_metadata);
                self.log.lemma_same_op_log_view_preserves_invariant(
                    pre_self.wrpm, self.wrpm, self.version_metadata, self.overall_metadata
                );
                lemma_persistent_memory_view_can_crash_as_committed(self.wrpm@);
            }

            let ghost mid_self = *self;
            self.log.abort_transaction(&mut self.wrpm, self.version_metadata, self.overall_metadata);

            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@,
                                                                     self.overall_metadata.main_table_addr as nat,
                                                                     self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.wrpm@,
                                                                     self.overall_metadata.item_table_addr as nat,
                                                                     self.overall_metadata.item_table_size as nat);
            let ghost list_area_subregion_view = get_subregion_view(self.wrpm@,
                                                                    self.overall_metadata.list_area_addr as nat,
                                                                    self.overall_metadata.list_area_size as nat);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    mid_self.wrpm@,
                    self.wrpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(mid_self);  

                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old(self).wrpm@.flush().committed(), self.wrpm@.committed(), self.version_metadata, self.overall_metadata);

                let old_main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(),
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion_view == old_main_table_subregion_view);

                pre_self.lemma_metadata_pending_allocs_are_invalid_at_abort();

                // TODO: refactor
                let pre_self_durable_bytes = pre_self.wrpm@.committed();
                let pre_self_tentative_bytes = Self::apply_physical_log_entries(pre_self.wrpm@.flush().committed(),
                    pre_self.log@.physical_op_list).unwrap();
                
                let pre_self_durable_main_table_region_state = extract_bytes(pre_self_durable_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let pre_self_tentative_main_table_region_state = extract_bytes(pre_self_tentative_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                
                let pre_self_durable_main_table_view = parse_main_table::<K>(pre_self_durable_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                let pre_self_tentative_main_table_view = parse_main_table::<K>(pre_self_tentative_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                
                pre_self.item_table.lemma_valid_indices_disjoint_with_free_and_pending_alloc(
                    pre_self.main_table@.valid_item_indices(),
                    pre_self_durable_main_table_view.valid_item_indices(), 
                    pre_self_tentative_main_table_view.valid_item_indices());
            }

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata),
                                              Ghost(self.main_table@.valid_item_indices()));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@),
                                                Ghost(self.overall_metadata));

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    pre_self.wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                assert(self.main_table@ == pre_self.main_table@);
                assert(self.item_table@ == pre_self.item_table@);
                assert(self.durable_list@ == pre_self.durable_list@);
            }

            assert(self@ == pre_self@);
        }

        fn abort_after_failed_main_table_tentative_create(
            &mut self,
            Ghost(old_self): Ghost<Self>,
            Ghost(pre_self): Ghost<Self>,
        )
            requires
                pre_self.inv(),
                !pre_self.transaction_committed(),
                old(self).inv(),
                old(self)@ == pre_self@,
                old(self).main_table.allocator_view() == pre_self.main_table.allocator_view(),
                old(self).main_table.pending_allocations_view() == pre_self.main_table.pending_allocations_view(),
                old(self).main_table.allocator_view().len() == 0,
                old(self) == (Self{ main_table: old(self).main_table, ..pre_self }),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    &&& forall|s| old(self).wrpm@.can_crash_as(s) ==> condition(s)
                    &&& condition(old(self).wrpm@.committed())
                }),
                old(self).main_table.inv(
                    get_subregion_view(old(self).wrpm@, old(self).overall_metadata.main_table_addr as nat,
                                       old(self).overall_metadata.main_table_size as nat),
                    old(self).overall_metadata
                ),
                old(self).main_table@ == pre_self.main_table@,
                old(self).main_table.allocator_inv(),
                old_self.inv(),
                old_self.constants() == pre_self.constants(),
                !old_self.transaction_committed(),
                old_self.wrpm@.len() == old(self).wrpm@.len(),
                pre_self == (Self{ item_table: pre_self.item_table, wrpm: pre_self.wrpm, ..old_self }),
                pre_self.item_table@ == old_self.item_table@,
                forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==>
                    old_self.wrpm@.state[addr] == pre_self.wrpm@.state[addr],
                forall|addr: int| old(self).version_metadata.overall_metadata_addr <= addr
                            < old(self).version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                    old_self.wrpm@.state[addr] == pre_self.wrpm@.state[addr],

                ({
                    let main_table_subregion_view = get_subregion_view(old(self).wrpm@,
                        old(self).overall_metadata.main_table_addr as nat,
                        old(self).overall_metadata.main_table_size as nat);
                    forall |s| #[trigger] main_table_subregion_view.can_crash_as(s) ==> 
                        parse_main_table::<K>(s, old(self).overall_metadata.num_keys, 
                            old(self).overall_metadata.main_table_entry_size) is Some
                }),
                forall|idx: u64| #[trigger] old(self).main_table@.valid_item_indices().contains(idx) ==> 
                    !old(self).item_table.allocator_view().contains(idx) && !old(self).item_table.pending_allocations_view().contains(idx),
                forall |idx: u64|0 <= idx < old(self).item_table.num_keys && !(#[trigger] old(self).main_table@.valid_item_indices().contains(idx)) ==> {
                    ||| old(self).item_table.pending_allocations_view().contains(idx)
                    ||| old(self).item_table.allocator_view().contains(idx)
                },
                forall |idx: u64| #[trigger] old(self).main_table.pending_allocations_view().contains(idx) ==> {
                    &&& !old(self).main_table.free_indices().contains(idx)
                    &&& old(self).main_table@.durable_main_table[idx as int] is None
                    &&& idx < old(self).overall_metadata.num_keys
                },
            ensures
                self.inv(),
                self@ == old_self@,
                self.constants() == pre_self.constants(),
                self.tentative_view() ==
                    Self::physical_recover_given_log(self.wrpm_view().flush().committed(),
                                                     self.spec_overall_metadata(), AbstractOpLogState::initialize()),
                !self.transaction_committed(),
                self.pending_allocations().is_empty(),
                self.pending_deallocations().is_empty(),
        {
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
                self.log.lemma_same_op_log_view_preserves_invariant(
                    pre_self.wrpm, self.wrpm, self.version_metadata, self.overall_metadata
                );
                lemma_persistent_memory_view_can_crash_as_committed(self.wrpm@);
            }

            let ghost mid_self = *self;
            self.log.abort_transaction(&mut self.wrpm, self.version_metadata, self.overall_metadata);

            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@,
                                                                     self.overall_metadata.main_table_addr as nat,
                                                                     self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.wrpm@,
                                                                     self.overall_metadata.item_table_addr as nat,
                                                                     self.overall_metadata.item_table_size as nat);
            let ghost list_area_subregion_view = get_subregion_view(self.wrpm@,
                                                                    self.overall_metadata.list_area_addr as nat,
                                                                    self.overall_metadata.list_area_size as nat);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    mid_self.wrpm@,
                    self.wrpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(mid_self);  

                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old(self).wrpm@.flush().committed(), self.wrpm@.committed(), self.version_metadata, self.overall_metadata);

                let old_main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(),
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion_view == old_main_table_subregion_view);
                assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
            }

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata),
                                              Ghost(self.main_table@.valid_item_indices()));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@),
                                                Ghost(self.overall_metadata));

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old_self.wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                assert(self.main_table@ == old_self.main_table@);
                assert(self.item_table@ == old_self.item_table@);
                assert(self.durable_list@ == old_self.durable_list@);
            }

            assert(self@ == old_self@);
        }

        exec fn abort_after_failed_read_operation(
            &mut self, 
            Tracked(perm): Tracked<&Perm>
        )
            requires 
                old(self).inv(),
                !old(self).transaction_committed(),
                old(self).pending_alloc_inv(),
                ({
                    let main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(), old(self).overall_metadata.main_table_addr as nat,
                        old(self).overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(main_table_subregion_view.committed(), old(self).overall_metadata.num_keys, 
                        old(self).overall_metadata.main_table_entry_size) is Some
                })
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                self.tentative_view() ==
                    Self::physical_recover_given_log(self.wrpm_view().flush().committed(),
                                                    self.spec_overall_metadata(), AbstractOpLogState::initialize()),
                !self.transaction_committed(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                self.pending_allocations().is_empty(),
                self.pending_deallocations().is_empty(),
        {
            proof { 
                lemma_persistent_memory_view_can_crash_as_committed(self.wrpm@); 
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
            }

            // first, abort the transaction within the op log
            self.log.abort_transaction(&mut self.wrpm, self.version_metadata, self.overall_metadata);

            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let ghost list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@,
                    self.wrpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(*old(self)); 

                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old(self).wrpm@.flush().committed(), self.wrpm@.committed(), self.version_metadata, self.overall_metadata);
                let old_main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(),
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion_view == old_main_table_subregion_view);

                old(self).lemma_metadata_pending_allocs_are_invalid_at_abort();

                // TODO: refactor
                let durable_bytes = old(self).wrpm@.committed();
                let tentative_bytes = Self::apply_physical_log_entries(old(self).wrpm@.flush().committed(),
                    old(self).log@.commit_op_log().physical_op_list).unwrap();
                let durable_main_table_region_state = extract_bytes(durable_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let tentative_main_table_region_state = extract_bytes(tentative_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                old(self).item_table.lemma_valid_indices_disjoint_with_free_and_pending_alloc(
                    old(self).main_table@.valid_item_indices(),
                    durable_main_table_view.valid_item_indices(),
                    tentative_main_table_view.valid_item_indices()
                );
            }

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata),
                                              Ghost(self.main_table@.valid_item_indices()));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@), Ghost(self.overall_metadata));
            
            proof {
                assert(!self.transaction_committed());
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();

                // These assertions help us prove that the pending allocation inv is restored
                let durable_state_bytes = self.wrpm@.committed();
                let tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list).unwrap();
                let durable_main_table_region = extract_bytes(durable_state_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(durable_state_bytes == tentative_state_bytes);
                assert(durable_main_table_region == main_table_subregion_view.committed());
                assert(main_table_subregion_view.can_crash_as(durable_main_table_region));
            }
        }

        exec fn abort_after_failed_op_log_append(
            &mut self,
            Ghost(pre_self): Ghost<Self>,
            Tracked(perm): Tracked<&Perm>,
        )
            requires 
                pre_self.inv(),
                !pre_self.transaction_committed(),
                !old(self).transaction_committed(),
                pre_self.pending_alloc_inv(),
                old(self).main_table.allocator_inv(),
                old(self).wrpm.inv(),
                old(self).overall_metadata == pre_self.overall_metadata,
                old(self).version_metadata == pre_self.version_metadata,
                old(self).wrpm@.len() == pre_self.wrpm@.len(),
                old(self).wrpm@.no_outstanding_writes(),
                views_differ_only_in_log_region(pre_self.wrpm@.flush(), old(self).wrpm@,
                    old(self).overall_metadata.log_area_addr as nat, old(self).overall_metadata.log_area_size as nat),
                UntrustedOpLog::<K, L>::recover(old(self).wrpm@.committed(), old(self).version_metadata, 
                    old(self).overall_metadata) == Some(AbstractOpLogState::initialize()),
                old(self).log@.physical_op_list.len() == 0,
                old(self).main_table.main_table_entry_size == old(self).overall_metadata.main_table_entry_size,
                old(self).main_table == pre_self.main_table,
                old(self).item_table == pre_self.item_table,
                old(self).log.inv(old(self).wrpm@, old(self).version_metadata, old(self).overall_metadata),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                ({
                    let tentative_view = self.tentative_view();
                    &&& tentative_view == Self::physical_recover_given_log(self.wrpm_view().flush().committed(), 
                            self.spec_overall_metadata(), AbstractOpLogState::initialize())
                    &&& self.pending_allocations().is_empty()
                    &&& self.pending_deallocations().is_empty()
                }),
        {
            // If the append failed, we need to abort the transaction and prove that the durable KV store as a whole
            // aborts the current transaction. The abort has already been initiated

            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let ghost list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    pre_self.wrpm@,
                    self.wrpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(pre_self); 
                
                pre_self.lemma_metadata_pending_allocs_are_invalid_at_abort();

                // TODO: refactor
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    pre_self.wrpm@.flush().committed(), self.wrpm@.committed(), self.version_metadata, self.overall_metadata);
                let old_main_table_subregion_view = get_subregion_view(pre_self.wrpm@.flush(),
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion_view == old_main_table_subregion_view);
                assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));

                let durable_bytes = pre_self.wrpm@.committed();
                let tentative_bytes = Self::apply_physical_log_entries(pre_self.wrpm@.flush().committed(),
                    pre_self.log@.commit_op_log().physical_op_list).unwrap();
                let durable_main_table_region_state = extract_bytes(durable_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let tentative_main_table_region_state = extract_bytes(tentative_bytes,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                pre_self.item_table.lemma_valid_indices_disjoint_with_free_and_pending_alloc(
                    pre_self.main_table@.valid_item_indices(),
                    durable_main_table_view.valid_item_indices(),
                    tentative_main_table_view.valid_item_indices()
                );
            }

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata),
                                              Ghost(self.main_table@.valid_item_indices()));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@), Ghost(self.overall_metadata));

            proof {
                assert(!self.transaction_committed());
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                
                // These assertions help us prove that the pending allocation inv is restored
                let durable_state_bytes = self.wrpm@.committed();
                let tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list).unwrap();
                let durable_main_table_region = extract_bytes(durable_state_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(durable_state_bytes == tentative_state_bytes);
                assert(durable_main_table_region == main_table_subregion_view.committed());
                assert(main_table_subregion_view.can_crash_as(durable_main_table_region));
            }
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
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(u64, u64), KvError<K>>)
            requires
                old(self).inv(),
                old(self).pending_alloc_inv(),
                !old(self).transaction_committed(),
                old(self).tentative_view() is Some,
                forall|s| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata())
                         == Some(old(self)@) ==> #[trigger] perm.check_permission(s),
            ensures
                self.inv(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                ({
                    match result {
                        Ok((offset, head_node)) => {
                            let spec_result = old(self).tentative_view().unwrap().create(offset as int, *key, *item);
                            match spec_result {
                                Ok(spec_result) => {
                                    let v1 = old(self).tentative_view().unwrap();
                                    let v2 = self.tentative_view().unwrap();
                                    &&& self.tentative_view() == Some(spec_result)
                                    &&& v2.len() == v1.len() + 1
                                    &&& v2.contains_key(offset as int)
                                    &&& v2[offset as int] is Some
                                    &&& self.pending_allocations() == old(self).pending_allocations().insert(offset)
                                    &&& self.pending_deallocations() == old(self).pending_deallocations()
                                }
                                Err(_) => false
                            }
                        },
                        Err(KvError::OutOfSpace) => {
                            &&& self@ == old(self)@
                            &&& self.tentative_view() ==
                                   Self::physical_recover_given_log(self.wrpm_view().flush().committed(),
                                                                    self.spec_overall_metadata(),
                                                                    AbstractOpLogState::initialize())
                            &&& self.pending_deallocations().is_empty()
                        },
                        Err(_) => false,
                    }
                })
        {
            // 1. find a free slot in the item table and tentatively write the new item there

            let ghost is_writable_item_table_addr = self.get_writable_mask_for_item_table();
            let ghost item_table_subregion_condition = self.condition_preserved_by_subregion_masks();
            proof {
                self.lemma_writable_mask_for_item_table_suitable_for_creating_subregion(perm);
            }
            let item_table_subregion = WriteRestrictedPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.wrpm,
                Tracked(perm),
                self.overall_metadata.item_table_addr,
                Ghost(self.overall_metadata.item_table_size as nat),
                Ghost(is_writable_item_table_addr),
                Ghost(item_table_subregion_condition),
            );

            let ghost tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            let ghost tentative_main_table_region = extract_bytes(tentative_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size).unwrap();
            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);

            // Establish some facts about the pending allocation invariants. When we tentatively write an item,
            // we'll break the item table's pending alloc invariant, but the metadata table invariant will 
            // be maintained.
            assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
            assert(main_table_subregion_view.committed() == extract_bytes(self.wrpm@.committed(),
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            assert(self.item_table.pending_alloc_inv(
                self.main_table@.valid_item_indices(), 
                self.main_table@.valid_item_indices(), 
                tentative_main_table_view.valid_item_indices()
            ));
            assert(self.main_table.pending_alloc_inv(main_table_subregion_view.committed(), 
                tentative_main_table_region, self.overall_metadata));

            let ghost self_before_tentative_item_write = *self;
            let item_index = match self.item_table.tentatively_write_item(
                &item_table_subregion,
                &mut self.wrpm,
                &item, 
                Tracked(perm),
                Ghost(self.overall_metadata),
                Ghost(self.main_table@.valid_item_indices()),
                Ghost(tentative_main_table_view.valid_item_indices()),
            ) {
                Ok(item_index) => item_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                            self_before_tentative_item_write, item_table_subregion, perm
                        );
                        assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.flush().committed()));
                        assert(main_table_subregion_view.flush() == get_subregion_view(self.wrpm@.flush(),
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                    }
                    self.abort_after_failed_item_table_tentatively_write_item(Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            };

            proof {
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                    self_before_tentative_item_write, item_table_subregion, perm
                );
                self.lemma_reestablish_inv_after_tentatively_write_item(*old(self), item_index, *item);

                // We also have to reestablish that this part of the metadata table pending allocation invariant is 
                // still true, as it is a precondition if we have to abort after a failed tentative create.

                assert forall |idx: u64| #[trigger] self.main_table.pending_allocations_view().contains(idx) implies {
                    &&& self.main_table@.durable_main_table[idx as int] is None
                } by {
                    assert(self.main_table.pending_alloc_check(idx, self.main_table@, tentative_main_table_view));
                } 
            }
            
            assert(self.inv());

            // 2. Just use a head index of 0 since the list should start empty.
            let head_index = 0;

            // 3. find a free slot in the metadata table and tentatively write a new entry to it
            let ghost is_writable_main_table_addr = self.get_writable_mask_for_main_table();
            let ghost main_table_subregion_condition = self.condition_preserved_by_subregion_masks();
            proof {
                self.lemma_writable_mask_for_main_table_suitable_for_creating_subregion(perm);
            }
            let main_table_subregion = WriteRestrictedPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.wrpm,
                Tracked(perm),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat),
                Ghost(is_writable_main_table_addr),
                Ghost(main_table_subregion_condition),
            );

            proof {
                self.lemma_main_table_subregion_grants_access_to_free_slots(main_table_subregion);
            }

            let ghost self_before_main_table_create = *self;
            let metadata_index = match self.main_table.tentative_create(
                &main_table_subregion,
                &mut self.wrpm,
                head_index, 
                item_index, 
                key,
                Tracked(perm),
                Ghost(self.overall_metadata),
            ) {
                Ok(metadata_index) => metadata_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                            self_before_main_table_create, main_table_subregion, perm
                        );
                    }
                    self.abort_after_failed_main_table_tentative_create(Ghost(*old(self)),
                                                                        Ghost(self_before_main_table_create));
                    return Err(e);
                }
            };


            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            proof {
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                    self_before_main_table_create, main_table_subregion, perm
                );
                self.log.lemma_same_op_log_view_preserves_invariant(old(self).wrpm, self.wrpm, self.version_metadata,
                                                                    self.overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
                    self.wrpm@.flush().committed(), self.version_metadata, self.overall_metadata,
                    self.log@.commit_op_log().physical_op_list
                );
                Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(),
                                                      self.log@.commit_op_log().physical_op_list);
            }

            // To tentatively validify a record, we need to obtain a log entry representing 
            // its validification and tentatively append it to the operation log.
            assert(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).committed() =~=
                   extract_bytes(self.wrpm@.committed(), self.overall_metadata.main_table_addr as nat,
                                 self.overall_metadata.main_table_size as nat));
            assert(parse_main_table::<K>(
                       get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                          self.overall_metadata.main_table_size as nat).committed(),
                       self.overall_metadata.num_keys,
                       self.overall_metadata.main_table_entry_size
                   ) == Some(self.main_table@)) by {
                lemma_persistent_memory_view_can_crash_as_committed(
                    get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat)
                );
            }
            assume(false);
            let log_entry = self.main_table.get_validify_log_entry(
                Ghost(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                         self.overall_metadata.main_table_size as nat)),
                metadata_index,
                Ghost(self.version_metadata), &self.overall_metadata, Ghost(tentative_view_bytes)
            );
            assume(false);

            /*

            // 4. tentatively append the new item's commit op to the log. Metadata entry commit 
            // implies item commit and also makes the list accessible so we can append to it
            let tracked fake_log_perm = TrustedPermission::fake_log_perm();
            let tracked fake_item_table_perm = TrustedItemTablePermission::fake_item_perm();
            let tracked fake_main_table_perm = TrustedMetadataPermission::fake_metadata_perm();

            let item_log_entry: OpLogEntryType<L> = OpLogEntryType::ItemTableEntryCommit { item_index };
            let metadata_log_entry: OpLogEntryType<L> = OpLogEntryType::CommitMetadataEntry { metadata_index };

            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &item_log_entry, Tracked(&fake_log_perm))?;
            self.log.tentatively_append_log_entry(&mut self.log_wrpm, kvstore_id, &metadata_log_entry, Tracked(&fake_log_perm))?;

            // 5. Add log entries to pending list
            self.pending_updates.push(item_log_entry);
            self.pending_updates.push(metadata_log_entry);

            // 6. Return the index of the metadata entry so it can be used in the volatile index.
            Ok((metadata_index, head_index))
            */
            Ok((0, 0))
        }

        proof fn lemma_update_item_index_log_entry_precondition(
            self,
            old_self: Self,
            index: u64, 
            item_index: u64,
            item_table_subregion: WriteRestrictedPersistentMemorySubregion,
            tentative_view_bytes: Seq<u8>,
            perm: &Perm
        )
            requires
                old_self.pending_alloc_inv(),
                old_self.inv(),
                self.inv(),
                item_table_subregion.inv(&self.wrpm, perm),
                old_self.item_table.allocator_view().contains(item_index),
                self.item_table.pending_allocations_view().contains(item_index),
                !old_self.main_table@.valid_item_indices().contains(item_index),
                !self.main_table@.valid_item_indices().contains(item_index),
                ({
                    let tentative_main_table = parse_main_table::<K>(extract_bytes(tentative_view_bytes,
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat),
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    old_self.item_table.pending_alloc_check(
                        item_index,
                        old_self.main_table@.valid_item_indices(),
                        old_self.main_table@.valid_item_indices(),
                        tentative_main_table.valid_item_indices())
                }),
                old_self.overall_metadata == self.overall_metadata,
                old_self.version_metadata == self.version_metadata,
                old_self.wrpm@.len() == self.wrpm@.len(),
                forall |s| #[trigger] old_self.wrpm_view().can_crash_as(s) ==> 
                    Self::physical_recover(s, self.spec_version_metadata(), self.spec_overall_metadata()) == Some(old_self@),
                    forall |s| #[trigger] old_self.wrpm_view().can_crash_as(s) ==> perm.check_permission(s),
                Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == Some(self@),
                Self::apply_physical_log_entries(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list) == Some(tentative_view_bytes),
                forall |s| Self::physical_recover(s, self.spec_version_metadata(), self.spec_overall_metadata()) == Some(old_self@)
                    ==> #[trigger] perm.check_permission(s),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                forall |addr: int| {
                    ||| 0 <= addr < self.overall_metadata.item_table_addr 
                    ||| self.overall_metadata.item_table_addr + self.overall_metadata.item_table_size <= addr < self.wrpm@.len()
                } ==> self.wrpm@.state[addr] == old_self.wrpm@.state[addr],
                ({
                    let tentative_view = old_self.tentative_view();
                    &&& tentative_view matches Some(tentative_view)
                    &&& tentative_view.contains_key(index as int)
                }),
                ({
                    let old_main_table_subregion = get_subregion_view(old_self.wrpm@, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let old_main_table = parse_main_table::<K>(old_main_table_subregion.committed(), 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    let old_item_table_subregion = get_subregion_view(old_self.wrpm@, 
                        self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                    let old_item_table = parse_item_table::<I, K>(old_item_table_subregion.committed(), 
                        self.overall_metadata.num_keys as nat, old_main_table.valid_item_indices()).unwrap();
                    &&& self.main_table@ == old_main_table
                })
            ensures
                Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == Some(self@),
                ({
                    let tentative_main_table = parse_main_table::<K>(extract_bytes(tentative_view_bytes,
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat),
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    !tentative_main_table.valid_item_indices().contains(item_index)                            
                }),

        {
            self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
            item_table_subregion.lemma_reveal_opaque_inv(&self.wrpm);
            assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));

            // 1. metadata table and list area have not been modified
            let old_main_table_subregion = get_subregion_view(old_self.wrpm@, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let current_main_table_subregion = get_subregion_view(self.wrpm@, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            
            assert(old_main_table_subregion == current_main_table_subregion);

            let old_list_area_subregion = get_subregion_view(old_self.wrpm@, 
                self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
            let current_list_area_subregion = get_subregion_view(self.wrpm@, 
                self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
            assert(old_list_area_subregion == current_list_area_subregion);

            // 2. item table view after commit is the same
            let old_item_table_subregion = get_subregion_view(old_self.wrpm@, 
                self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let current_item_table_subregion = get_subregion_view(self.wrpm@, 
                self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);

            // 3. after applying log, all components recover to the same state they did before
            Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.wrpm@.committed(), 
                self.version_metadata, self.overall_metadata, self.log@.commit_op_log().physical_op_list);

            let old_main_table = parse_main_table::<K>(old_main_table_subregion.committed(), 
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            let tentative_main_table = parse_main_table::<K>(extract_bytes(tentative_view_bytes,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat),
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            assert(self.main_table@ == old_main_table);
            assert(self.main_table@.valid_item_indices() == old_main_table.valid_item_indices());

            let old_item_table = parse_item_table::<I, K>(old_item_table_subregion.committed(), 
                self.overall_metadata.num_keys as nat, old_main_table.valid_item_indices()).unwrap();

            let tentative_item_table = parse_item_table::<I, K>(extract_bytes(tentative_view_bytes,
                self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat),
                self.overall_metadata.num_keys as nat, tentative_main_table.valid_item_indices()).unwrap();
            
            assert(old_item_table_subregion.can_crash_as(old_item_table_subregion.committed()));
            assert(old_item_table_subregion.committed() == extract_bytes(old_self.wrpm@.committed(),
                self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));

            // the pending alloc check holds for this index, which proves that it is now pending allocation
            assert(old_self.item_table.pending_alloc_check(item_index,
                                                           old_main_table.valid_item_indices(),
                                                           old_main_table.valid_item_indices(),
                                                           tentative_main_table.valid_item_indices()));
        }

        proof fn lemma_tentative_view_after_appending_update_item_log_entry_includes_new_log_entry(
            self,
            old_self: Self,
            index: u64,
            item_index: u64,
            item: I,
            log_entry: PhysicalOpLogEntry,
            tentative_view_bytes: Seq<u8>,
        )
            requires 
                self.inv(),
                old_self.inv(),
                !self.transaction_committed(),
                !old_self.transaction_committed(),
                forall |s| #[trigger] old_self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, old_self.version_metadata, self.overall_metadata) == Some(old_self@),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(old_self@),
                self.version_metadata == old_self.version_metadata,
                self.overall_metadata == old_self.overall_metadata,
                old_self.tentative_view() is Some,
                self.wrpm@.len() == old_self.wrpm@.len(),
                self.log@.physical_op_list == old_self.log@.physical_op_list.push(log_entry@),
                tentative_view_bytes.len() == self.wrpm@.len(),
                views_differ_only_in_log_region(self.wrpm@, old_self.wrpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                ({
                    let old_flushed_mem = old_self.wrpm@.flush().committed();
                    let old_op_log = old_self.log@.commit_op_log().physical_op_list;
                    let old_mem_with_old_log_installed = Self::apply_physical_log_entries(old_flushed_mem, old_op_log);
                    let old_mem_old_log_main_table_region = extract_bytes(old_mem_with_old_log_installed.unwrap(), 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let old_main_table_view = parse_main_table::<K>(old_mem_old_log_main_table_region, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    &&& old_mem_with_old_log_installed matches Some(old_mem_with_old_log_installed)
                    &&& tentative_view_bytes == old_mem_with_old_log_installed
                    &&& old_main_table_view matches Some(old_main_table_view)
                    &&& old_main_table_view.durable_main_table[index as int] matches Some(entry) 
                    &&& !old_main_table_view.valid_item_indices().contains(item_index)
                }),
                ({
                    let new_mem = tentative_view_bytes.map(|pos: int, pre_byte: u8|
                        if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                            log_entry.bytes[pos - log_entry.absolute_addr]
                        } else {
                            pre_byte
                        }
                    );
                    let current_main_table_region = extract_bytes(tentative_view_bytes, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    let old_item_index = current_main_table_view.durable_main_table[index as int].unwrap().item_index();
                    
                    &&& self.overall_metadata.main_table_addr <= log_entry.absolute_addr
                    &&& log_entry.absolute_addr + log_entry.len <=
                        self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size
                    &&& log_entry@.inv(self.version_metadata, self.overall_metadata)

                    // after applying this log entry to the current tentative state,
                    // this entry's metadata index has been updated
                    &&& new_main_table_view is Some
                    &&& new_main_table_view == current_main_table_view.update_item_index(index as int, item_index)
                    &&& new_main_table_view.unwrap().valid_item_indices() == 
                            current_main_table_view.valid_item_indices().insert(item_index).remove(old_item_index)
                }),
                self.item_table.outstanding_item_table@ == old_self.item_table.outstanding_item_table@,
                self.item_table.outstanding_item_table@[item_index as int] == Some(item),
                item_index < self.overall_metadata.num_keys,
            ensures 
                self.tentative_view() is Some,
                old_self.tentative_view().unwrap().len() == self.tentative_view().unwrap().len(),
                self.tentative_view().unwrap() == old_self.tentative_view().unwrap().update_item(index as int, item).unwrap(),
        {
            broadcast use pmcopy_axioms;

            self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
            lemma_valid_entry_index(index as nat, self.overall_metadata.num_keys as nat, self.overall_metadata.main_table_entry_size as nat);

            let old_flushed_mem = old_self.wrpm@.flush().committed();
            let flushed_mem = self.wrpm@.flush().committed();
            let old_op_log = old_self.log@.commit_op_log().physical_op_list;
            let op_log = self.log@.commit_op_log().physical_op_list;
            

            assert(op_log.subrange(0, old_op_log.len() as int) == old_op_log);
            assert(AbstractPhysicalOpLogEntry::log_inv(op_log, self.version_metadata, self.overall_metadata));
            assert(AbstractPhysicalOpLogEntry::log_inv(old_op_log, self.version_metadata, self.overall_metadata));


            Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(flushed_mem, self.version_metadata,
                self.overall_metadata, op_log);
            Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(flushed_mem, self.version_metadata,
                self.overall_metadata, old_op_log);
            Self::lemma_log_replay_preserves_size(flushed_mem, op_log);
            Self::lemma_log_replay_preserves_size(flushed_mem, old_op_log);

            let mem_with_old_log_applied = Self::apply_physical_log_entries(flushed_mem, old_op_log).unwrap();
            let mem_with_new_log_applied = Self::apply_physical_log_entries(flushed_mem, op_log).unwrap();

            assert(Self::apply_physical_log_entry(mem_with_old_log_applied, log_entry@).unwrap() == mem_with_new_log_applied);

            let new_mem = tentative_view_bytes.map(|pos: int, pre_byte: u8|
                if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                    log_entry.bytes[pos - log_entry.absolute_addr]
                } else {
                    pre_byte
                }
            );
            lemma_establish_extract_bytes_equivalence(tentative_view_bytes, new_mem);

            // Is this whole thing actually useful?
            assert(states_differ_only_in_log_region(old_flushed_mem, flushed_mem,
                self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
            Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old_flushed_mem, flushed_mem,
                old_op_log, self.version_metadata, self.overall_metadata);
            // tentative_view_bytes is old mem with old log applied; mem_with_old_log_applied is new mem with 
            // old log applied. They still differ only in the log region.
            assert(states_differ_only_in_log_region(tentative_view_bytes, mem_with_old_log_applied,
                self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));

            // The only part modified by this log entry is the main table.

            // assert(states_differ_only_in_log_region(mem_with_new_log_applied, new_mem, 
            //     self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
            let old_tentative_main_table_region = extract_bytes(tentative_view_bytes, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let mem_with_old_log_applied_main_table_region = extract_bytes(mem_with_old_log_applied, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let mem_with_new_log_applied_main_table_region = extract_bytes(mem_with_new_log_applied, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let new_mem_main_table_region = extract_bytes(new_mem, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            lemma_establish_extract_bytes_equivalence(mem_with_old_log_applied_main_table_region, new_mem_main_table_region);

            assert(mem_with_new_log_applied_main_table_region == new_mem_main_table_region);

            assert(old_tentative_main_table_region == mem_with_old_log_applied_main_table_region);

            let old_tentative_main_table = parse_main_table::<K>(old_tentative_main_table_region,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            let mem_with_old_log_applied_main_table = parse_main_table::<K>(mem_with_old_log_applied_main_table_region,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            let mem_with_new_log_applied_main_table = parse_main_table::<K>(mem_with_new_log_applied_main_table_region,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            let new_mem_main_table = parse_main_table::<K>(new_mem_main_table_region,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();     
            assert(mem_with_new_log_applied_main_table == new_mem_main_table);
            let old_item_index = old_tentative_main_table.durable_main_table[index as int].unwrap().item_index();

            // The other regions recover successfully
            let old_item_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let old_list_area_region = extract_bytes(tentative_view_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
            let new_log_item_table_region = extract_bytes(mem_with_new_log_applied, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let new_log_list_area_region = extract_bytes(mem_with_new_log_applied, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
            let new_item_table_region = extract_bytes(new_mem, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let new_list_area_region = extract_bytes(new_mem, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

            assert(old_item_table_region == new_item_table_region);
            assert(old_list_area_region == new_list_area_region);

            assert(new_log_item_table_region == new_item_table_region);
            assert(new_log_list_area_region == new_list_area_region);

            assert(parse_item_table::<I, K>(
                new_item_table_region,
                self.overall_metadata.num_keys as nat,
                old_tentative_main_table.valid_item_indices()
            ) is Some);

            // we know that the old tentative main table valid indices parse to a valid item table
            // but we need to know that the new ones do 
            assert(new_mem_main_table.valid_item_indices() == 
                old_tentative_main_table.valid_item_indices().insert(item_index).remove(old_item_index));

            // assert(!old_tentative_main_table.valid_item_indices().contains(item_index));
            // assert(old_tentative_main_table.valid_item_indices().contains(old_item_index));

            // assert(forall |idx: u64| {
            //     &&& new_mem_main_table.valid_item_indices().contains(idx) 
            //     &&& !old_tentative_main_table.valid_item_indices().contains(idx) 
            // } ==> idx == item_index);
            Self::lemma_item_table_bytes_unchanged_by_applying_log_entries(self.wrpm@.flush().committed(),
                self.log@.physical_op_list, self.version_metadata, self.overall_metadata);

            assert(extract_bytes(self.wrpm@.flush().committed(), self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) ==
            extract_bytes(new_mem, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));

            let item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let old_item_table_subregion_view = get_subregion_view(old_self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);

            assert(item_table_subregion_view.flush().committed() == new_item_table_region);
            assert(old_item_table_subregion_view.flush().committed() == old_item_table_region);


            // both of these should have an outstanding item, we haven't committed anything yet
            assert(old_self.item_table.outstanding_item_table@[item_index as int] == Some(item));
            assert(self.item_table.outstanding_item_table@[item_index as int] == Some(item));

            assert(self.item_table.outstanding_item_table_entry_matches_pm_view(
                item_table_subregion_view,
                item_index as int
            ));
            assert(old_self.item_table.outstanding_item_table_entry_matches_pm_view(
                item_table_subregion_view,
                item_index as int
            ));

            assert(item_table_subregion_view.flush().committed() == new_item_table_region);

            let entry_size = I::spec_size_of() + u64::spec_size_of();
            assert forall |idx: u64| new_mem_main_table.valid_item_indices().contains(idx) implies {
                let offset = index_to_offset(idx as nat, entry_size);
                &&& validate_item_table_entry::<I, K>(extract_bytes(new_item_table_region, offset, entry_size))
                &&& idx != item_index ==> parse_item_entry::<I, K>(extract_bytes(new_item_table_region, offset, entry_size)) == 
                        parse_item_entry::<I, K>(extract_bytes(old_item_table_region, offset, entry_size))
                &&& idx == item_index ==> parse_item_entry::<I, K>(extract_bytes(new_item_table_region, offset, entry_size)) == Some(item)
            } by {
                let offset = index_to_offset(idx as nat, entry_size);
                let bytes = extract_bytes(new_item_table_region, offset, entry_size);

                lemma_valid_entry_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);
                lemma_entries_dont_overlap_unless_same_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);
                
                if !old_tentative_main_table.valid_item_indices().contains(idx) {
                    assert(idx == item_index);

                    assert(self.item_table.outstanding_item_table@[item_index as int] == Some(item));
                    assert(self.item_table.outstanding_item_table_entry_matches_pm_view(
                        item_table_subregion_view,
                        item_index as int
                    ));
                    
                    assert(bytes == extract_bytes(old_item_table_region, offset, entry_size));
                    assert(outstanding_bytes_match(item_table_subregion_view, offset as int, bytes));
                    assert(outstanding_bytes_match(item_table_subregion_view, offset as int, spec_crc_bytes(I::spec_to_bytes(item))));
                    assert(outstanding_bytes_match(item_table_subregion_view, (offset + u64::spec_size_of()) as int, I::spec_to_bytes(item)));

                    lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, offset as int, spec_crc_bytes(I::spec_to_bytes(item)));
                    lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, (offset + u64::spec_size_of()) as int, I::spec_to_bytes(item));

                    assert(extract_bytes(new_item_table_region, offset, u64::spec_size_of()) == spec_crc_bytes(I::spec_to_bytes(item)));
                    assert(extract_bytes(new_item_table_region, offset + u64::spec_size_of(), I::spec_size_of()) == I::spec_to_bytes(item));
                    lemma_subrange_of_extract_bytes_equal(new_item_table_region, offset, offset, entry_size, u64::spec_size_of());
                    lemma_subrange_of_extract_bytes_equal(new_item_table_region, offset, offset + u64::spec_size_of(), entry_size, I::spec_size_of());
                    
                    assert(validate_item_table_entry::<I, K>(extract_bytes(new_item_table_region, offset, entry_size)));
                } // else, trivial
            }

            let new_item_table = parse_item_table::<I, K>(
                new_item_table_region,
                self.overall_metadata.num_keys as nat,
                new_mem_main_table.valid_item_indices()
            );
            assert(new_item_table is Some);

            // TODO WITH LIST IMPLEMENTATION
            assume(DurableList::<K, L>::parse_all_lists(
                new_mem_main_table,
                new_list_area_region,
                self.overall_metadata.list_node_size,
                self.overall_metadata.num_list_entries_per_node
            ) == DurableList::<K, L>::parse_all_lists(
                old_tentative_main_table,
                old_list_area_region,
                self.overall_metadata.list_node_size,
                self.overall_metadata.num_list_entries_per_node
            ));

            assert(Self::physical_recover_after_applying_log(mem_with_new_log_applied, self.overall_metadata, self.log@) is Some);

            let old_tentative_view = old_self.tentative_view().unwrap();
            let new_tentative_view = self.tentative_view().unwrap();

            assert(old_tentative_view.contains_key(index as int));

            assert(old_self.tentative_view() is Some);
            assert(old_tentative_view.update_item(index as int, item) is Ok);
            assert(old_tentative_view.contents.dom() == old_self.tentative_view().unwrap().update_item(index as int, item).unwrap().contents.dom());
            assert(old_tentative_view.len() == old_tentative_view.update_item(index as int, item).unwrap().len());
            
            
            assert(new_tentative_view.contents.dom() == old_tentative_view.update_item(index as int, item).unwrap().contents.dom());

            assert(new_tentative_view.contents == old_tentative_view.update_item(index as int, item).unwrap().contents);
        }

        pub fn tentative_update_item(
            &mut self,
            offset: u64,
            item: &I,
            kvstore_id: u128,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(), KvError<K>>)
            requires 
                old(self).inv(),
                old(self)@.contains_key(offset as int),
                !old(self).transaction_committed(),
                !old(self).pending_deallocations().contains(offset),
                old(self).pending_alloc_inv(),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> 
                    Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                forall |s| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).wrpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).wrpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).wrpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    &&& tentative_view matches Some(tentative_view)
                    &&& tentative_view.contains_key(offset as int)
                }),
            ensures 
                self.inv(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                match result {
                    Ok(()) => {
                        let spec_result = old(self).tentative_view().unwrap().update_item(offset as int, *item);
                        match spec_result {
                            Ok(spec_result) => {
                                let v1 = old(self).tentative_view().unwrap();
                                let v2 = self.tentative_view().unwrap();
                                &&& v2 == spec_result
                                &&& v2.len() == v1.len()
                                &&& v2[offset as int].unwrap().item == item
                                &&& self.pending_allocations() == old(self).pending_allocations()
                                &&& self.pending_deallocations() == old(self).pending_deallocations()
                            }
                            Err(_) => false
                        }
                    }
                    Err(KvError::OutOfSpace) => {
                        &&& self@ == old(self)@
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.wrpm_view().flush().committed(),
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                        &&& self.pending_deallocations().is_empty()
                    }
                    Err(_) => false,
                }
        {
            // 1. find a free slot in the item table and tentatively write the new item there
            let ghost is_writable_item_table_addr = self.get_writable_mask_for_item_table();
            let ghost item_table_subregion_condition = self.condition_preserved_by_subregion_masks();
            proof {
                self.lemma_writable_mask_for_item_table_suitable_for_creating_subregion(perm);
            }

            let item_table_subregion = WriteRestrictedPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.wrpm,
                Tracked(perm),
                self.overall_metadata.item_table_addr,
                Ghost(self.overall_metadata.item_table_size as nat),
                Ghost(is_writable_item_table_addr),
                Ghost(item_table_subregion_condition),
            );

            let main_table_subregion = PersistentMemorySubregion::new(
                self.wrpm.get_pm_region_ref(),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                // Establish that we can replay the log and that this does not change its size.
                assert(Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list) is Some);
                Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), 
                    self.log@.commit_op_log().physical_op_list);
            }

            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            let ghost tentative_main_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size).unwrap();
            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            
            // Establish some facts about the pending allocation invariants. When we tentatively write an item,
            // we'll break the item table's pending alloc invariant, but the metadata table invariant will 
            // be maintained.
            assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
            assert(main_table_subregion_view.committed() == extract_bytes(self.wrpm@.committed(),
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            assert(self.item_table.pending_alloc_inv(
                self.main_table@.valid_item_indices(), 
                self.main_table@.valid_item_indices(), 
                tentative_main_table_view.valid_item_indices()));
            assert(self.main_table.pending_alloc_inv(main_table_subregion_view.committed(), 
                tentative_main_table_region, self.overall_metadata));

            let ghost self_before_tentative_item_write = *self;
            let item_index = match self.item_table.tentatively_write_item(
                &item_table_subregion,
                &mut self.wrpm,
                &item, 
                Tracked(perm),
                Ghost(self.overall_metadata),
                Ghost(self.main_table@.valid_item_indices()),
                Ghost(tentative_main_table_view.valid_item_indices()),
            ) {
                Ok(item_index) => item_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                            self_before_tentative_item_write, item_table_subregion, perm
                        );
                        assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.flush().committed()));
                        assert(main_table_subregion_view.flush() == get_subregion_view(self.wrpm@.flush(),
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                    }
                    self.abort_after_failed_item_table_tentatively_write_item(Ghost(*old(self)),
                                                                              Tracked(perm));
                    return Err(e);
                }
            };

            let ghost pre_append_tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
    
            proof {
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                    self_before_tentative_item_write, item_table_subregion, perm);
                item_table_subregion.lemma_reveal_opaque_inv(&self.wrpm);
                self.lemma_reestablish_inv_after_tentatively_write_item(
                    *old(self), item_index, *item
                );
            }

            let pm = self.wrpm.get_pm_region_ref();

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
                
                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.wrpm@.flush().committed(),
                    self.version_metadata, self.overall_metadata, self.log@.commit_op_log().physical_op_list);
                Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);

                // Prove that this operation has not modified the main table, log, or list 
                assert forall |addr: int| {
                    ||| self.overall_metadata.main_table_addr <= addr < self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size 
                    ||| self.overall_metadata.log_area_addr <= addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size
                    ||| self.overall_metadata.list_area_addr <= addr < self.overall_metadata.list_area_addr + self.overall_metadata.list_area_size 
                } implies pre_append_tentative_view_bytes[addr] == tentative_view_bytes[addr]
                by {
                    Self::lemma_byte_equal_after_recovery_specific_byte(addr, old(self).wrpm@.flush().committed(), 
                        self.wrpm@.flush().committed(), self.version_metadata, self.overall_metadata, self.log@.commit_op_log().physical_op_list);
                }
                assert(extract_bytes(pre_append_tentative_view_bytes, self.overall_metadata.main_table_addr as nat, 
                    self.overall_metadata.main_table_size as nat) == extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                assert(extract_bytes(pre_append_tentative_view_bytes, self.overall_metadata.log_area_addr as nat, 
                    self.overall_metadata.log_area_size as nat) == extract_bytes(tentative_view_bytes, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
                assert(extract_bytes(pre_append_tentative_view_bytes, self.overall_metadata.list_area_addr as nat, 
                    self.overall_metadata.list_area_size as nat) == extract_bytes(tentative_view_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat));          

                let pre_append_tentative_main_table = parse_main_table::<K>(extract_bytes(pre_append_tentative_view_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat), 
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                let tentative_item_table_bytes = extract_bytes(tentative_view_bytes, 
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let pre_append_tentative_item_table_bytes = extract_bytes(pre_append_tentative_view_bytes, 
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let tentative_item_table = parse_item_table::<I, K>(tentative_item_table_bytes, 
                    self.overall_metadata.num_keys as nat, tentative_main_table_view.valid_item_indices());
                let pre_append_tentative_item_table = parse_item_table::<I, K>(pre_append_tentative_item_table_bytes, 
                    self.overall_metadata.num_keys as nat, pre_append_tentative_main_table.valid_item_indices());

                // Replaying the log does not change the item table bytes. This depends on a KV store invariant
                Self::lemma_item_table_bytes_unchanged_by_applying_log_entries(old(self).wrpm@.flush().committed(),
                    old(self).log@.physical_op_list, self.version_metadata, self.overall_metadata);
                Self::lemma_item_table_bytes_unchanged_by_applying_log_entries(self.wrpm@.flush().committed(),
                    self.log@.physical_op_list, self.version_metadata, self.overall_metadata);
                // These assertions hit some necessary triggers to use the postconditions of the above proofs.
                assert(forall |addr: int| {
                    &&& 0 <= addr < self.wrpm@.len()
                    &&& self.overall_metadata.item_table_addr <= addr < self.overall_metadata.item_table_addr + self.overall_metadata.item_table_size
                } ==> #[trigger] pre_append_tentative_view_bytes[addr] == self.wrpm@.flush().committed()[addr]);
                assert(forall |addr: int| {
                    &&& 0 <= addr < self.wrpm@.len()
                    &&& self.overall_metadata.item_table_addr <= addr < self.overall_metadata.item_table_addr + self.overall_metadata.item_table_size
                } ==> #[trigger] tentative_view_bytes[addr] == old(self).wrpm@.flush().committed()[addr]);

                let current_item_table_subregion = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                assert(current_item_table_subregion.flush().committed() == pre_append_tentative_item_table_bytes);
                let old_item_table_subregion = get_subregion_view(old(self).wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                assert(old_item_table_subregion.flush().committed() == tentative_item_table_bytes);

                // After flushing, any outstanding bytes in the item table have now become durable.
                // We prove that all outstanding updates become durable in the new tentative view
                // and that all outstanding updates except for the one to `item_index` become
                // durable in the old tentative view (because it wasn't outstanding then.)
                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert forall |idx: u64| {
                    &&& idx < self.overall_metadata.num_keys 
                    &&& self.item_table.outstanding_item_table@[idx as int] is Some 
                } implies {
                    let start = index_to_offset(idx as nat, entry_size as nat);
                    let i = self.item_table.outstanding_item_table@[idx as int].unwrap();
                    &&& extract_bytes(current_item_table_subregion.flush().committed(), start, u64::spec_size_of()) == spec_crc_bytes(I::spec_to_bytes(i))
                    &&& extract_bytes(current_item_table_subregion.flush().committed(), start + u64::spec_size_of(), I::spec_size_of()) == I::spec_to_bytes(i)
                    &&& idx != item_index ==> ({
                            &&& extract_bytes(old_item_table_subregion.flush().committed(), start, u64::spec_size_of()) == spec_crc_bytes(I::spec_to_bytes(i))
                            &&& extract_bytes(old_item_table_subregion.flush().committed(), start + u64::spec_size_of(), I::spec_size_of()) == I::spec_to_bytes(i)
                        })
                } by {
                    broadcast use pmcopy_axioms;

                    let start = index_to_offset(idx as nat, entry_size as nat);
                    let i = self.item_table.outstanding_item_table@[idx as int].unwrap();

                    lemma_valid_entry_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);
                    lemma_entries_dont_overlap_unless_same_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);

                    // these assertions are required to hit triggers
                    assert(self.item_table.outstanding_item_table_entry_matches_pm_view(current_item_table_subregion, idx as int));
                    assert(outstanding_bytes_match(current_item_table_subregion, start as int, spec_crc_bytes(I::spec_to_bytes(i))));
                    assert(outstanding_bytes_match(current_item_table_subregion, (start + u64::spec_size_of()) as int, I::spec_to_bytes(i)));
                    lemma_outstanding_bytes_match_after_flush(current_item_table_subregion, start as int, spec_crc_bytes(I::spec_to_bytes(i)));
                    lemma_outstanding_bytes_match_after_flush(current_item_table_subregion, (start + u64::spec_size_of()) as int, I::spec_to_bytes(i));

                    if idx != item_index {
                        assert(old(self).item_table.outstanding_item_table_entry_matches_pm_view(old_item_table_subregion, idx as int));
                        assert(outstanding_bytes_match(old_item_table_subregion, start as int, spec_crc_bytes(I::spec_to_bytes(i))));
                        assert(outstanding_bytes_match(old_item_table_subregion, (start + u64::spec_size_of()) as int, I::spec_to_bytes(i)));
                        lemma_outstanding_bytes_match_after_flush(old_item_table_subregion, start as int, spec_crc_bytes(I::spec_to_bytes(i)));
                        lemma_outstanding_bytes_match_after_flush(old_item_table_subregion, (start + u64::spec_size_of()) as int, I::spec_to_bytes(i));
                    }
                }

                // Prove that for all indexes besides the newly-updated item index, the underlying bytes
                // are the same in the two tentative states.
                assert forall |idx: u64| {
                    &&& idx < self.overall_metadata.num_keys 
                    &&& idx != item_index
                } implies {
                    let offset = #[trigger] index_to_offset(idx as nat, entry_size as nat);
                    extract_bytes(pre_append_tentative_item_table_bytes, offset, entry_size) == 
                        extract_bytes(tentative_item_table_bytes, offset, entry_size)
                } by {
                    let start = index_to_offset(idx as nat, entry_size as nat);
                    lemma_valid_entry_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);
                    lemma_entries_dont_overlap_unless_same_index(idx as nat, self.overall_metadata.num_keys as nat, entry_size);
                    if self.item_table.outstanding_item_table@[idx as int] is Some {
                        // we've previously asserted that the CRC and item, extracted separately, match the outstanding entry,
                        // so to prove equality here we just need a few additional assertions about `extract_bytes`
                        assert(extract_bytes(current_item_table_subregion.flush().committed(), start, u64::spec_size_of()) + 
                            extract_bytes(current_item_table_subregion.flush().committed(), start + u64::spec_size_of(), I::spec_size_of()) ==
                                extract_bytes(current_item_table_subregion.flush().committed(), start, entry_size));
                        assert(extract_bytes(current_item_table_subregion.flush().committed(), start, entry_size) == 
                            extract_bytes(old_item_table_subregion.flush().committed(), start, entry_size));
                    } else {
                        // else, there was no outstanding entry, so we just have to prove that flush is a no op on these bytes.
                        assert(self.item_table.outstanding_item_table_entry_matches_pm_view(current_item_table_subregion, idx as int));
                        assert(old(self).item_table.outstanding_item_table_entry_matches_pm_view(old_item_table_subregion, idx as int));
                        assert(extract_bytes(current_item_table_subregion.flush().committed(), start, entry_size) == extract_bytes(current_item_table_subregion.committed(), start, entry_size));
                        assert(extract_bytes(old_item_table_subregion.flush().committed(), start, entry_size) == extract_bytes(old_item_table_subregion.committed(), start, entry_size));
                    }
                }

                // Prove that we satisfy the precondition to obtain this log entry. The postcondition of this 
                // lemma also helps prove that the tentative view has not changed.
                self.lemma_update_item_index_log_entry_precondition(*old(self), offset, item_index, 
                    item_table_subregion, pre_append_tentative_view_bytes, perm);

                assert(pre_append_tentative_item_table == tentative_item_table);
                assert(self.tentative_view() == old(self).tentative_view());
            }

            // 2. Create a log entry that will overwrite the metadata table entry
            // with a new one containing the new item table index
            let log_entry = match self.main_table.create_update_item_index_log_entry(
                &main_table_subregion,
                pm,
                offset,
                item_index,
                &self.overall_metadata,
                Ghost(self.version_metadata),
                Ghost(pre_append_tentative_view_bytes), 
            ) {
                Ok(log_entry) => log_entry,
                Err(e) => {
                    // TODO @hayley
                    // also need to handle abort cases where the failing op didn't 
                    // change anything but there are outstanding modifications
                    assume(false);
                    return Err(e);
                }
            };

            // Create a crash predicate for the append operation and prove that it ensures the append
            // will be crash consistent.
            let ghost crash_pred = |s: Seq<u8>| {
                Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
            };
            proof {
                let committed_log = self.log@.commit_op_log();
                let flushed_mem = self.wrpm@.flush().committed();

                Self::lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(flushed_mem,
                    self.version_metadata, self.overall_metadata, committed_log.physical_op_list);
                self.lemma_tentative_log_entry_append_is_crash_safe(crash_pred, perm);                 
            }

            let ghost committed_log = self.log@.commit_op_log();
            let ghost log_with_new_entry = self.log@.tentatively_append_log_entry(log_entry@).commit_op_log();
            let ghost current_flushed_mem = self.wrpm@.flush().committed();

            let ghost recovery_state_with_new_log = Self::physical_recover_given_log(current_flushed_mem, self.overall_metadata, log_with_new_entry);

            // 3. Append the log entry to the operation log.
            let ghost pre_append_self = *self;
            // let ghost pre_append_wrpm = self.wrpm;
            let result = self.log.tentatively_append_log_entry(&mut self.wrpm, &log_entry, self.version_metadata, self.overall_metadata, Ghost(crash_pred), Tracked(perm));
            match result {
                Ok(()) => {}
                Err(e) => {
                    // TODO @hayley
                    // this is also different from the abort delete case, because 
                    // the item table was modified too
                    assume(false);
                    return Err(e);
                }
            }

            self.pending_updates.push(log_entry);
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                
                // We have to prove that each component's invariant holds after appending the new log entry,
                // which is straightforward because they held beforehand and the append operation does 
                // not modify any of their bytes.
                assert(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat) == get_subregion_view(old(self).wrpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat));
                assert(self.main_table.inv(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat), self.overall_metadata));
                
                assert(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                    self.overall_metadata.list_area_size as nat) == get_subregion_view(old(self).wrpm@, 
                    self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat));
                assert(self.durable_list.inv(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                    self.overall_metadata.list_area_size as nat), self.main_table@, self.overall_metadata));
                
                assert(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat) == get_subregion_view(pre_append_self.wrpm@, 
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));
                assert(self.item_table.inv(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                                                              self.overall_metadata.item_table_size as nat),
                                           self.overall_metadata,
                                           self.main_table@.valid_item_indices()));

                // Prove that all crash states still recover to the current state. We already know this for each 
                // component, since it's part of their invariants, so we just need to prove that it's true 
                // for the whole KV store as well.
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                
                self.lemma_tentative_view_after_appending_update_item_log_entry_includes_new_log_entry(pre_append_self, offset, 
                    item_index, *item, log_entry, pre_append_tentative_view_bytes);
            }

            Ok(())
        }

        proof fn lemma_committed_subregion_equal_to_extracted_bytes(
            pm: PersistentMemoryRegionView,
            start: nat,
            len: nat
        )
            requires 
                start + len <= pm.len(),
            ensures 
                get_subregion_view(pm, start, len).committed() == extract_bytes(pm.committed(), start, len)
        {
            assert(get_subregion_view(pm, start, len).committed() =~= extract_bytes(pm.committed(), start, len));
        }

        proof fn lemma_tentative_view_after_appending_delete_log_entry_includes_new_log_entry(
            self,
            old_self: Self,
            index: u64, 
            item_index: u64,
            log_entry: PhysicalOpLogEntry,
            tentative_view_bytes: Seq<u8>,
        )
            requires 
                old_self.valid(),
                old_self@.contains_key(index as int),
                !old_self.transaction_committed(),
                !self.transaction_committed(),
                old_self.pending_alloc_inv(),
                forall |s| #[trigger] old_self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, old_self.version_metadata, self.overall_metadata) == Some(old_self@),
                self.version_metadata == old_self.version_metadata,
                self.overall_metadata == old_self.overall_metadata,
                self.wrpm@.len() == old_self.wrpm@.len(),
                ({
                    let flushed_mem = self.wrpm@.flush().committed();
                    let old_flushed_mem = old_self.wrpm@.flush().committed();
                    states_differ_only_in_log_region(flushed_mem, old_flushed_mem, self.overall_metadata.log_area_addr as nat,
                        self.overall_metadata.log_area_size as nat)
                }),
                old_self.wrpm@.len() >= VersionMetadata::spec_size_of(),
                no_outstanding_writes_to_version_metadata(old_self.wrpm@),
                no_outstanding_writes_to_overall_metadata(old_self.wrpm@, self.version_metadata.overall_metadata_addr as int),
                no_outstanding_writes_to_version_metadata(self.wrpm@),
                no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                AbstractPhysicalOpLogEntry::log_inv(old_self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                self.overall_metadata.main_table_addr <= log_entry.absolute_addr,
                log_entry.absolute_addr + log_entry.len <=
                    self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size,
                old_self.tentative_view() matches Some(tentative_view) && tentative_view.contains_key(index as int),
                0 <= index < self.main_table@.durable_main_table.len(),
                ({
                    let old_flushed_mem = old_self.wrpm@.flush().committed();
                    let old_op_log = old_self.log@.commit_op_log().physical_op_list;
                    let old_mem_with_old_log_installed = Self::apply_physical_log_entries(old_flushed_mem, old_op_log);
                    let old_mem_old_log_main_table_region = extract_bytes(old_mem_with_old_log_installed.unwrap(), 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let old_main_table_view = parse_main_table::<K>(old_mem_old_log_main_table_region, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    &&& old_mem_with_old_log_installed matches Some(old_mem_with_old_log_installed)
                    &&& tentative_view_bytes == old_mem_with_old_log_installed
                    &&& old_main_table_view matches Some(old_main_table_view)
                    &&& old_main_table_view.durable_main_table[index as int] matches Some(entry) 
                    &&& entry.item_index() == item_index
                }),
                ({
                    // This is what we know about the log entry. We have to do some additional work
                    // to prove that replaying it gets us the result we want
                    let new_mem = tentative_view_bytes.map(|pos: int, pre_byte: u8|
                        if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                            log_entry.bytes[pos - log_entry.absolute_addr]
                        } else {
                            pre_byte
                        }
                    );
                    let current_main_table_region = extract_bytes(tentative_view_bytes, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    let item_index = self.main_table@.durable_main_table[index as int].unwrap().item_index();
                    &&& new_main_table_view is Some
                    &&& new_main_table_view == current_main_table_view.delete(index as int)
                    &&& new_main_table_view.unwrap().valid_item_indices() == current_main_table_view.valid_item_indices().remove(item_index)
                }),
                get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat) == 
                    get_subregion_view(old_self.wrpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat),
                get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) == 
                    get_subregion_view(old_self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat),
                get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat) == 
                    get_subregion_view(old_self.wrpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat),
                self.log@.physical_op_list == old_self.log@.physical_op_list.push(log_entry@),
            ensures 
                ({
                    let flushed_mem = self.wrpm@.flush().committed();
                    let old_flushed_mem = old_self.wrpm@.flush().committed();
                    let op_log = self.log@.commit_op_log().physical_op_list;
                    let old_op_log = old_self.log@.commit_op_log().physical_op_list;

                    let old_mem_with_old_log_installed = Self::apply_physical_log_entries(old_flushed_mem, old_op_log).unwrap();
                    let old_mem_with_new_log_installed = Self::apply_physical_log_entries(old_flushed_mem, op_log).unwrap();
                    let new_mem_with_new_log_installed = Self::apply_physical_log_entries(flushed_mem, op_log).unwrap();
                
                    let old_mem_old_log_main_table_region = extract_bytes(old_mem_with_old_log_installed, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let old_mem_old_log_item_table_region = extract_bytes(old_mem_with_old_log_installed, 
                        self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                    let old_mem_old_log_list_area_region = extract_bytes(old_mem_with_old_log_installed, 
                        self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

                    let old_mem_new_log_item_table_region = extract_bytes(old_mem_with_new_log_installed, 
                        self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                    let old_mem_new_log_list_area_region = extract_bytes(old_mem_with_new_log_installed, 
                        self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
                    
                    let new_mem_new_log_main_table_region = extract_bytes(new_mem_with_new_log_installed, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let new_mem_new_log_list_area_region = extract_bytes(new_mem_with_new_log_installed, 
                        self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

                    let old_main_table_view = parse_main_table::<K>(old_mem_old_log_main_table_region, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    let main_table_view = parse_main_table::<K>(new_mem_new_log_main_table_region, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    
                    &&& old_mem_old_log_item_table_region == old_mem_new_log_item_table_region
                    &&& old_mem_old_log_list_area_region == old_mem_new_log_list_area_region
                    &&& main_table_view == old_main_table_view.delete(index as int).unwrap()
                    &&& main_table_view.valid_item_indices() == old_main_table_view.valid_item_indices().remove(item_index)

                    &&& DurableList::<K, L>::parse_all_lists(main_table_view, new_mem_new_log_list_area_region, 
                            self.overall_metadata.list_node_size, self.overall_metadata.num_list_entries_per_node) is Some

                    &&& extracted_regions_match(old_mem_with_new_log_installed, new_mem_with_new_log_installed, self.overall_metadata)
                    &&& deserialize_version_metadata(old_mem_with_new_log_installed) == deserialize_version_metadata(new_mem_with_new_log_installed)
                    &&& deserialize_overall_metadata(old_mem_with_new_log_installed, self.version_metadata.overall_metadata_addr) == 
                            deserialize_overall_metadata(new_mem_with_new_log_installed, self.version_metadata.overall_metadata_addr)

                    &&& Self::apply_physical_log_entries(old_flushed_mem, op_log) is Some
                    &&& Self::apply_physical_log_entries(flushed_mem, op_log) is Some
                    &&& states_differ_only_in_log_region(new_mem_with_new_log_installed, old_mem_with_new_log_installed, self.overall_metadata.log_area_addr as nat,
                            self.overall_metadata.log_area_size as nat)
                })
        {
            assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));
            assert(old_self.wrpm@.can_crash_as(old_self.wrpm@.committed()));
            
            let flushed_mem = self.wrpm@.flush().committed();
            let old_flushed_mem = old_self.wrpm@.flush().committed();
            let op_log = self.log@.commit_op_log().physical_op_list;
            let old_op_log = old_self.log@.commit_op_log().physical_op_list;

            // this assertions helps establish that replaying the old op log is equivalent to 
            // replaying a prefix of the new op log
            assert(old_op_log == op_log.subrange(0, old_op_log.len() as int));

            Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(flushed_mem, old_flushed_mem, 
                op_log, self.version_metadata, self.overall_metadata);

            let old_mem_with_old_log_installed = Self::apply_physical_log_entries(old_flushed_mem, old_op_log).unwrap();
            let old_mem_with_new_log_installed = Self::apply_physical_log_entries(old_flushed_mem, op_log).unwrap();
            let new_mem_with_new_log_installed = Self::apply_physical_log_entries(flushed_mem, op_log).unwrap();

            Self::lemma_log_replay_preserves_size(old_flushed_mem, old_op_log);
            Self::lemma_log_replay_preserves_size(old_flushed_mem, op_log);
            Self::lemma_log_replay_preserves_size(flushed_mem, op_log);

            let old_mem_old_log_main_table_region = extract_bytes(old_mem_with_old_log_installed, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let old_mem_old_log_item_table_region = extract_bytes(old_mem_with_old_log_installed, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let old_mem_old_log_list_area_region = extract_bytes(old_mem_with_old_log_installed, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

            let old_mem_new_log_item_table_region = extract_bytes(old_mem_with_new_log_installed, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let old_mem_new_log_list_area_region = extract_bytes(old_mem_with_new_log_installed, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

            let new_mem_new_log_main_table_region = extract_bytes(new_mem_with_new_log_installed, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let new_mem_new_log_list_area_region = extract_bytes(new_mem_with_new_log_installed, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

            lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                old_mem_with_new_log_installed, new_mem_with_new_log_installed, self.version_metadata, self.overall_metadata);
        
            assert(old_mem_old_log_item_table_region == old_mem_new_log_item_table_region);
            assert(old_mem_old_log_list_area_region == old_mem_new_log_list_area_region);

            let old_main_table_view = parse_main_table::<K>(old_mem_old_log_main_table_region, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
            let main_table_view = parse_main_table::<K>(new_mem_new_log_main_table_region, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
        
            assert(main_table_view == old_main_table_view.delete(index as int).unwrap());
            assert(old_main_table_view.durable_main_table[index as int] matches Some(entry) && entry.item_index() == item_index);
            assert(main_table_view.valid_item_indices() == old_main_table_view.valid_item_indices().remove(item_index));

            DurableList::<K, L>::lemma_parse_all_lists_succeeds_after_record_delete(
                old_main_table_view,
                main_table_view,
                old_mem_old_log_main_table_region,
                new_mem_new_log_list_area_region,
                index as int,
                self.overall_metadata.list_node_size,
                self.overall_metadata.num_list_entries_per_node
            );
        }

        proof fn lemma_item_index_is_currently_valid(self, index: u64, item_index: u64)
            requires 
                self.valid(),
                self@.contains_key(index as int),
                self.pending_alloc_inv(),
                !self.item_table.pending_deallocations_view().contains(item_index),
                self.main_table@.valid_item_indices().contains(item_index),
                ({
                    &&& self.main_table@.durable_main_table[index as int] matches Some(entry)
                    &&& entry.item_index() == item_index
                }),
            ensures 
                
                !self.item_table.pending_allocations_view().contains(item_index),
                !self.item_table.allocator_view().contains(item_index),
                ({
                    let flushed_mem = self.wrpm@.flush().committed();
                    let op_log = self.log@.commit_op_log().physical_op_list;
                    let tentative_view_bytes = Self::apply_physical_log_entries(flushed_mem, op_log);
                    let tentative_main_table_region = extract_bytes(tentative_view_bytes.unwrap(), 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    &&& tentative_view_bytes matches Some(tentative_view_bytes)
                    &&& tentative_main_table_view matches Some(tentative_main_table_view)
                    &&& tentative_main_table_view.valid_item_indices().contains(item_index)
                })
        {

            let flushed_mem = self.wrpm@.flush().committed();
            let op_log = self.log@.commit_op_log().physical_op_list;

            let tentative_view_bytes = Self::apply_physical_log_entries(flushed_mem, op_log).unwrap();
            let tentative_main_table_region = extract_bytes(tentative_view_bytes, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                self.overall_metadata.main_table_entry_size).unwrap();
            
            let durable_state_bytes = self.wrpm@.committed();
            let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let durable_main_table_subregion = get_subregion_view(self.wrpm@, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let durable_main_table_view = parse_main_table::<K>(durable_main_table_region, self.overall_metadata.num_keys,
                self.overall_metadata.main_table_entry_size).unwrap();
            
            assert(durable_main_table_subregion.can_crash_as(durable_main_table_region));
            assert(self.main_table@ == durable_main_table_view);
            assert(self.item_table.pending_alloc_check(item_index,
                                                       self.main_table@.valid_item_indices(),
                                                       self.main_table@.valid_item_indices(),
                                                       tentative_main_table_view.valid_item_indices()));

        }


        pub fn tentative_delete(
            &mut self,
            index: u64,
            Tracked(perm): Tracked<&Perm>
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                old(self)@.contains_key(index as int),
                !old(self).transaction_committed(),
                !old(self).pending_deallocations().contains(index),
                old(self).pending_alloc_inv(),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> 
                    Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                forall |s| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    ==> #[trigger] perm.check_permission(s),
                Self::physical_recover(old(self).wrpm_view().committed(), old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                no_outstanding_writes_to_version_metadata(old(self).wrpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).wrpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).wrpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    &&& tentative_view matches Some(tentative_view)
                    &&& tentative_view.contains_key(index as int)
                }),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                match result {
                    Ok(()) => {
                        // in the tentative view of the log, the key has been removed
                        let tentative_view = self.tentative_view();
                        &&& tentative_view matches Some(tentative_view)
                        &&& !tentative_view.contains_key(index as int)
                        &&& self.pending_allocations() == old(self).pending_allocations()
                        &&& self.pending_deallocations() == old(self).pending_deallocations().insert(index)
                    }
                    Err(e) => {
                        // transaction has been aborted due to an error in the log
                        // this drops all outstanding modifications to the kv store
                        let tentative_view = self.tentative_view();
                        &&& tentative_view == Self::physical_recover_given_log(self.wrpm_view().flush().committed(), 
                              self.spec_overall_metadata(), AbstractOpLogState::initialize())
                        &&& self.pending_allocations().is_empty()
                        &&& self.pending_deallocations().is_empty()
                    }
                }
        {
            assert(forall |idx: u64| old(self).main_table.allocator_view().contains(idx) ==> idx < self.overall_metadata.num_keys);
            let pm = self.wrpm.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(
                pm,
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);

                // These asserts establish that the main table subregion recovers properly, which is 
                // a precondition of some of the fns that handle aborted transactions later on.
                let main_table_subregion_view = get_subregion_view(self.wrpm@,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(forall |s| #[trigger] main_table_subregion_view.can_crash_as(s) ==>
                    parse_main_table::<K>(s, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) is Some);
                assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.flush().committed()));
                assert(main_table_subregion_view.flush() == get_subregion_view(self.wrpm@.flush(),
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            }

            // We have to read the current item index from the entry so that we can 
            // properly deallocate it later.
            // TODO: could the caller pass this in? Would it be easier/faster?
            let (key, metadata) = match self.main_table.get_key_and_metadata_entry_at_index(
                &main_table_subregion, pm, index, Ghost(self.overall_metadata)) 
            {
                Ok((key, metadata)) => (key, metadata),
                Err(e) => {
                    self.abort_after_failed_read_operation(Tracked(perm));
                    return Err(e);
                }
            };
            let item_index = metadata.item_index;

            // check that this item index is not already pending deallocation. This could happen 
            // if we, e.g., update the item in this same transaction. if it is, abort the 
            // transaction.
            // TODO: it might be fine to just ignore this? aborting the transaction 
            // is likely overkill, but it might complicate other things to not abort
            if self.item_table.index_pending_deallocation(item_index) {
                self.abort_after_failed_read_operation(Tracked(perm));
                return Err(KvError::EntryIsNotValid);
            }

            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            proof { 
                Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);
                self.lemma_item_index_is_currently_valid(index, item_index);
            }

            // To tentatively delete a record, we need to obtain a log entry representing 
            // its deletion and tentatively append it to the operation log.
            assert(get_subregion_view(self.wrpm@, main_table_subregion.start(), main_table_subregion.len()).committed() =~=
                extract_bytes(self.wrpm@.committed(), self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            assert(parse_main_table::<K>(get_subregion_view(self.wrpm@, main_table_subregion.start(), main_table_subregion.len()).committed(),
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@)) 
            by {
                    lemma_persistent_memory_view_can_crash_as_committed(
                        get_subregion_view(self.wrpm@, main_table_subregion.start(),
                                           main_table_subregion.len())
                    );
            }
            let log_entry = self.main_table.create_delete_log_entry(
                Ghost(get_subregion_view(self.wrpm@, main_table_subregion.start(),
                                         main_table_subregion.len())),
                Ghost(self.wrpm@), index,
                Ghost(self.version_metadata), &self.overall_metadata, Ghost(tentative_view_bytes));
    
            let ghost crash_pred = |s: Seq<u8>| {
                Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
            };

            proof {
                self.lemma_tentative_log_entry_append_is_crash_safe(crash_pred, perm);
            }

            let ghost committed_log = self.log@.commit_op_log();
            let ghost log_with_new_entry = self.log@.tentatively_append_log_entry(log_entry@).commit_op_log();
            let ghost current_flushed_mem = self.wrpm@.flush().committed();

            let ghost recovery_state_with_new_log = Self::physical_recover_given_log(current_flushed_mem, self.overall_metadata, log_with_new_entry);

            proof {
                // We want to prove that if we append this log entry to the log, then replaying it will get us into the state we want.

                // replaying the current committed log onto current_flushed_mem should give us the tentative view
                assert(self.tentative_view() == Self::physical_recover_given_log(current_flushed_mem, self.overall_metadata, committed_log));
                assert(committed_log.physical_op_list == log_with_new_entry.physical_op_list.subrange(0, committed_log.physical_op_list.len() as int));
                assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));
            }

            // then append it to the operation log
            let ghost pre_self = *self;
            let result = self.log.tentatively_append_log_entry(&mut self.wrpm, &log_entry, self.version_metadata, self.overall_metadata, Ghost(crash_pred), Tracked(perm));
            match result {
                Ok(()) => {}
                Err(e) => {

                    self.abort_after_failed_op_log_append(Ghost(pre_self), Tracked(perm));
                    return Err(e);
                }
            }

            self.pending_updates.push(log_entry);
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            proof {
                // We need to prove that the current tentative view of the KV store (i.e., the state if we commit right now)
                // is the same as the state we would obtain by replaying the log. The key challenge here is that 
                // the tentative append changed the log's pending bytes, so the old and new pm states are 
                // not identical, and we don't know exactly how the bytes were changed. However, we do know the 
                // abstract log in both cases, so we can prove that replaying that log results in the same state.

                assert(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat) == 
                    get_subregion_view(old(self).wrpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                assert(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) == 
                    get_subregion_view(old(self).wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));
                assert(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat) == 
                    get_subregion_view(old(self).wrpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat));

                self.lemma_tentative_view_after_appending_delete_log_entry_includes_new_log_entry(*old(self), index, item_index, log_entry,
                    tentative_view_bytes);

                let flushed_mem = self.wrpm@.flush().committed();
                let old_flushed_mem = old(self).wrpm@.flush().committed();
                let op_log = self.log@.commit_op_log().physical_op_list;
                let old_op_log = old(self).log@.commit_op_log().physical_op_list;

                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                );
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
            }

            // tentatively deallocate the indexes associated with this record.
            // they won't actually be deallocated until we commit the transaction
            // so that we don't accidentally reallocate them while they are 
            // still in use by a valid record.

            // We have new tentative bytes since we've appended a new entry to the log
            let ghost new_tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                self.log@.commit_op_log().physical_op_list).unwrap();
            let ghost tentative_main_table_subregion_state = extract_bytes(new_tentative_view_bytes, 
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_subregion_state,
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

            proof {
                let durable_main_table_subregion_state = extract_bytes(self.wrpm@.committed(), 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_subregion_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                Self::lemma_committed_subregion_equal_to_extracted_bytes(old(self).wrpm@, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.wrpm@, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);   

                let old_tentative_main_table_subregion_state = extract_bytes(tentative_view_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let old_tentative_main_table_view = parse_main_table::<K>(old_tentative_main_table_subregion_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                assert forall |idx: u64| 0 <= idx < durable_main_table_view.durable_main_table.len() && idx != index implies 
                    self.main_table.pending_alloc_check(idx, durable_main_table_view, tentative_main_table_view)
                by { assert(old(self).main_table.pending_alloc_check(idx, durable_main_table_view, old_tentative_main_table_view)); }

                assert(old(self).main_table.pending_alloc_check(index, durable_main_table_view, old_tentative_main_table_view));
                assert(!self.main_table.pending_deallocations_view().contains(index));
            }

            let ghost main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let ghost list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);
            assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));

            self.main_table.tentatively_deallocate_entry(Ghost(main_table_subregion_view),
                index, Ghost(self.overall_metadata), Ghost(new_tentative_view_bytes));

            proof {
                let durable_main_table_subregion_state = extract_bytes(self.wrpm@.committed(), 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_subregion_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                let old_tentative_main_table_subregion_state = extract_bytes(tentative_view_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let old_tentative_main_table_view = parse_main_table::<K>(old_tentative_main_table_subregion_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                assert(self.main_table@.valid_item_indices() == old(self).main_table@.valid_item_indices());

                assert(tentative_main_table_view.valid_item_indices() == old_tentative_main_table_view.valid_item_indices().remove(item_index));
               
                assert(self.main_table@ == durable_main_table_view);
                
                assert forall |idx: u64| {
                    &&& 0 <= idx < self.overall_metadata.num_keys 
                    &&& idx != item_index  
                } implies self.item_table.pending_alloc_check(idx,
                                                              self.main_table@.valid_item_indices(), 
                                                              self.main_table@.valid_item_indices(), 
                                                              tentative_main_table_view.valid_item_indices())
                by { 
                    assert(old(self).item_table.pending_alloc_check(idx,
                                                                  self.main_table@.valid_item_indices(),
                                                                  self.main_table@.valid_item_indices(),
                                                                  old_tentative_main_table_view.valid_item_indices()));
                    assert(self.item_table.pending_deallocations_view() == old(self).item_table.pending_deallocations_view());
                    assert(self.item_table.pending_allocations_view() == old(self).item_table.pending_allocations_view()); 
                    assert(self.item_table.allocator_view() == old(self).item_table.allocator_view());
                }

                assert(!tentative_main_table_view.valid_item_indices().contains(item_index));

                // To prove that this index is not valid or pending in the current item table,
                // we'll compare the current valid indices against the *old* tentative state's valid 
                // item indices. The current tentative state's valid item indices have changed, but
                // the contents of the free/valid/alloc sets have not, so we can use the fact that 
                // the pending alloc invariant holds for the old tentative state to prove what 
                // we need to about the current item table's indexes.
                self.item_table.lemma_valid_indices_disjoint_with_free_and_pending_alloc(
                    self.main_table@.valid_item_indices(),
                    self.main_table@.valid_item_indices(),
                    old_tentative_main_table_view.valid_item_indices()
                );
            }
            self.item_table.tentatively_deallocate_item(Ghost(item_table_subregion_view), item_index, 
                Ghost(self.overall_metadata), Ghost(self.main_table@.valid_item_indices()),
                Ghost(tentative_main_table_view.valid_item_indices()), Ghost(new_tentative_view_bytes));

            assert(self.pending_alloc_inv());

            Ok(())
        }

        proof fn lemma_if_every_component_recovers_to_its_current_state_then_self_does(self)
            requires
                !self.transaction_committed(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr,
                                                  self.overall_metadata.kvstore_id),
                self.wrpm@.len() == self.overall_metadata.region_size,
                self.log.inv(self.wrpm@, self.version_metadata, self.overall_metadata),
                self.main_table.inv(get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                                                           self.overall_metadata.main_table_size as nat),
                                        self.overall_metadata),
                self.item_table.inv(get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata, self.main_table@.valid_item_indices()),
                self.durable_list.inv(get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                                                         self.overall_metadata.list_area_size as nat),
                                      self.main_table@, self.overall_metadata),
                forall|s| #[trigger] self.wrpm@.can_crash_as(s) ==> self.version_metadata == deserialize_version_metadata(s),
                forall|s| #[trigger] self.wrpm@.can_crash_as(s) ==>
                    self.overall_metadata == deserialize_overall_metadata(
                        s,
                        self.version_metadata.overall_metadata_addr
                    ),
            ensures
                forall|s| #[trigger] self.wrpm@.can_crash_as(s) ==> self.inv_mem(s)
        {
            let overall_metadata = self.overall_metadata;
            assert forall|s| #[trigger] self.wrpm@.can_crash_as(s) implies self.inv_mem(s) by {
                assert(self.version_metadata == deserialize_version_metadata(s));
                assert(self.overall_metadata == deserialize_overall_metadata(
                    s,
                    self.version_metadata.overall_metadata_addr
                ));
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
                assert(UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata) ==
                       Some(AbstractOpLogState::initialize()));
                assert(Self::apply_physical_log_entries(s, AbstractOpLogState::initialize().physical_op_list) =~=
                       Some(s));
                lemma_subregion_view_can_crash_as_subrange(self.wrpm@, s, overall_metadata.main_table_addr as nat,
                                                           overall_metadata.main_table_size as nat);
                lemma_subregion_view_can_crash_as_subrange(self.wrpm@, s, overall_metadata.item_table_addr as nat,
                                                           overall_metadata.item_table_size as nat);
                lemma_subregion_view_can_crash_as_subrange(self.wrpm@, s, overall_metadata.list_area_addr as nat,
                                                           overall_metadata.list_area_size as nat);
                assert(Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@));
            }
        }

        proof fn lemma_commit_log_precondition(
            self,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            perm: &Perm,
        )
            requires 
                self.valid(),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> perm.check_permission(s),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s: Seq<u8>| {
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == self.tentative_view()
                } <==> crash_pred(s),
                self.tentative_view() is Some,
                !self.transaction_committed(),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@),
                forall |s| {
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == self.tentative_view()
                } ==> #[trigger] perm.check_permission(s),
                self.spec_num_log_entries_in_current_transaction() > 0,
                !self.transaction_committed(),
                no_outstanding_writes_to_version_metadata(self.wrpm@),
                no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int),
                self.wrpm@.len() >= VersionMetadata::spec_size_of(),
            ensures
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                } ==> #[trigger] crash_pred(s2),
                forall |s2: Seq<u8>| {
                    let flushed_state = self.wrpm@.flush().committed();
                    &&& flushed_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(flushed_state, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& {
                            ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@.commit_op_log())
                            ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    }
                } ==> perm.check_permission(s2),
        {
            self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
            Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);

            // Prove that the crash predicate satisfies the preconditions about it, which specify how we can crash
            // before and after `commit_log` flushes the device.
            assert forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
            } implies #[trigger] crash_pred(s2) by { self.lemma_durable_kv_satisfies_crash_condition_with_init_op_log(s1, s2, crash_pred); }
            
            assert forall |s2: Seq<u8>| {
                let flushed_state = self.wrpm@.flush().committed();
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(flushed_state, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                &&& {
                        ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@.commit_op_log())
                        ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                }
            } implies perm.check_permission(s2) by {
                let flushed_state = self.wrpm@.flush().committed();
                assert(self.wrpm@.can_crash_as(flushed_state));
                if UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@.commit_op_log()) {
                    // The CDB made it to storage.
                    // In this case, the whole KV store recovers to its tentative view. 
                    let committed_log = self.log@.commit_op_log();

                    Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                        flushed_state, s2, committed_log.physical_op_list, self.version_metadata, self.overall_metadata);
                    Self::lemma_log_replay_preserves_size(s2, committed_log.physical_op_list);
                    let flushed_state_with_log_installed = Self::apply_physical_log_entries(flushed_state, committed_log.physical_op_list).unwrap();
                    let s2_with_log_installed = Self::apply_physical_log_entries(s2, committed_log.physical_op_list).unwrap();

                    assert(states_differ_only_in_log_region(flushed_state_with_log_installed, s2_with_log_installed, 
                        self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        flushed_state_with_log_installed, s2_with_log_installed, self.version_metadata, self.overall_metadata);
                } else {
                    // The CDB did not make it to storage.
                    assert(UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()));
                    self.lemma_durable_kv_satisfies_crash_condition_with_init_op_log(flushed_state, s2, crash_pred);
                }
            }
            assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));
        }

        proof fn lemma_can_clear_op_log_after_commit(
            self,
            old_self: Self,
            pre_log_install_wrpm: WriteRestrictedPersistentMemoryRegion<Perm, PM>,
            pre_log_install_op_log: AbstractOpLogState,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            perm: &Perm,
        )
            requires
                self.wrpm.inv(),
                pre_log_install_wrpm.inv(),
                self.log.inv(pre_log_install_wrpm@, self.version_metadata, self.overall_metadata),
                forall |s: Seq<u8>| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) <==> crash_pred(s),
                forall |s| #[trigger] crash_pred(s) ==> perm.check_permission(s),
                self.wrpm@.no_outstanding_writes(),
                pre_log_install_wrpm@.no_outstanding_writes(),
                crash_pred(self.wrpm@.committed()),
                self.wrpm@.len() == self.overall_metadata.region_size,
                self.wrpm@.len() == pre_log_install_wrpm@.len(),
                self.wrpm@.len() == self.overall_metadata.region_size,
                self.wrpm@.len() == pre_log_install_wrpm@.len(),
                self.transaction_committed(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr, self.overall_metadata.kvstore_id),
                UntrustedOpLog::<K, L>::recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == Some(self.log@),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                extract_bytes(pre_log_install_wrpm@.committed(), self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat) ==
                    extract_bytes(self.wrpm@.committed(), self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == 
                    Self::physical_recover_given_log(self.wrpm@.committed(), self.overall_metadata, AbstractOpLogState::initialize()),
            ensures 
                forall |s2: Seq<u8>| {
                    let current_state = self.wrpm@.flush().committed();
                    &&& current_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(s2, current_state, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& {
                            ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@)
                            ||| UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                        }
                } ==> #[trigger] crash_pred(s2),
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(self.log@)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@)
                } ==> #[trigger] crash_pred(s2),
                self.log.inv(self.wrpm@, self.version_metadata, self.overall_metadata),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> crash_pred(s),
                forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata) == Some(self.log@),
        {
            let current_mem = self.wrpm@.committed();
            let old_mem_with_log_installed = Self::apply_physical_log_entries(pre_log_install_wrpm@.committed(), 
                pre_log_install_op_log.physical_op_list).unwrap();
            let pre_install_subregion = get_subregion_view(pre_log_install_wrpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);
            let current_subregion = get_subregion_view(self.wrpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);
            let pre_install_extract_bytes = extract_bytes(pre_log_install_wrpm@.committed(), self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);

            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(self.wrpm@);
            assert(forall |s| self.wrpm@.can_crash_as(s) ==> s == self.wrpm@.committed());

            // Next, we need to prove that the log subregions of the pre-install PM and current PM
            // are identical, so that we can prove that the op log invariant holds after log install.
            assert forall |addr: int| 0 <= addr < self.overall_metadata.log_area_size implies 
                pre_install_subregion.state[addr] == current_subregion.state[addr] 
            by {
                assert(pre_install_subregion.state[addr].state_at_last_flush == pre_install_extract_bytes[addr]);
                assert(pre_install_subregion.state[addr].outstanding_write is None);
                assert(current_subregion.state[addr].outstanding_write is None);
            }
            assert(pre_install_subregion == current_subregion);
            self.log.lemma_same_op_log_view_preserves_invariant(pre_log_install_wrpm, self.wrpm, self.version_metadata, self.overall_metadata);

            // By now we've also met the preconditions of this lemma that proves that we can safely 
            // clear the log
            Self::lemma_clear_log_is_crash_safe(self.wrpm, self.log, self.version_metadata,
                self.overall_metadata, crash_pred, self@, perm);
        }


        // Commits all pending updates by committing the log and applying updates to 
        // each durable component.
        pub fn commit(
            &mut self,
            Tracked(perm): Tracked<&Perm>
        ) -> (result: Result<(), KvError<K>>)
            requires 
                old(self).valid(),
                !old(self).transaction_committed(),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> perm.check_permission(s),
                forall |s| #[trigger] old(self).wrpm_view().can_crash_as(s) ==> 
                    Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                forall |s| {
                    ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == old(self).tentative_view()
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).wrpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).wrpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).wrpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    tentative_view is Some
                }),
                old(self).spec_num_log_entries_in_current_transaction() > 0,
                old(self).pending_alloc_inv(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                self.pending_allocations().is_empty(),
                self.pending_deallocations().is_empty(),
                match result {
                    Ok(()) => {
                        // The old tentative view is now our current state
                        let old_tentative_view = old(self).tentative_view();
                        &&& old_tentative_view matches Some(old_tentative_view)
                        &&& self@ == old_tentative_view
                    }
                    Err(e) => {
                        // Transaction has been aborted due to an error in the log.
                        // This can happen during commit if we don't have enough space to 
                        // write the CRC when committing the oplog.
                        // All outstanding writes to the KV store are dropped.
                        let tentative_view = self.tentative_view();
                        tentative_view == Self::physical_recover_given_log(self.wrpm_view().flush().committed(), 
                            self.spec_overall_metadata(), AbstractOpLogState::initialize())
                    }
                }
        {
            let ghost tentative_view_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list).unwrap();

            // 1. Create the crash predicate for the commit operation.
            // This predicate will allow either the current durable state or the current tentative state
            let ghost crash_pred = |s: Seq<u8>| {
                ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == self.tentative_view()
            };

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.wrpm, self.version_metadata, self.overall_metadata);
                Self::lemma_log_replay_preserves_size(self.wrpm@.flush().committed(), self.log@.commit_op_log().physical_op_list);
                self.lemma_commit_log_precondition(crash_pred, perm);
                assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));
            }

            // 2. Commit the op log
            let ghost pre_self = *self;
            match self.log.commit_log(&mut self.wrpm, self.version_metadata, 
                self.overall_metadata, Ghost(crash_pred), Tracked(perm)) 
            {
                Ok(()) => {}
                Err(e) => {
                    // If the append failed, we need to abort the transaction and prove that the durable KV store as a whole
                    // aborts the current transaction.
                    let ghost main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);      
                    let ghost item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat); 
                    let ghost list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                        self.overall_metadata.list_area_size as nat);

                    proof {
                        Self::lemma_metadata_unchanged_when_views_differ_only_in_log_region(
                            old(self).wrpm@,
                            self.wrpm@,
                            self.version_metadata,
                            self.overall_metadata
                        );
                        self.lemma_transaction_abort(*old(self));

                        old(self).lemma_metadata_pending_allocs_are_invalid_at_abort();

                        lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                            old(self).wrpm@.flush().committed(), self.wrpm@.committed(), self.version_metadata, self.overall_metadata);
                        let old_main_table_subregion_view = get_subregion_view(old(self).wrpm@.flush(),
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        assert(main_table_subregion_view == old_main_table_subregion_view);
                        assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.committed()));
        
                        let durable_main_table_region_state = extract_bytes(old(self).wrpm@.committed(),
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        let tentative_main_table_region_state = extract_bytes(tentative_view_bytes,
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        let durable_main_table_view = parse_main_table::<K>(durable_main_table_region_state,
                            self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                        let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region_state,
                            self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                        old(self).item_table.lemma_valid_indices_disjoint_with_free_and_pending_alloc(
                            old(self).main_table@.valid_item_indices(),
                            durable_main_table_view.valid_item_indices(),
                            tentative_main_table_view.valid_item_indices()
                        );
                    }

                    // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
                    self.pending_updates = Vec::new();
                    assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

                    // abort the transaction in each component to re-establish their invariants
                    self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
                    self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata),
                                                      Ghost(self.main_table@.valid_item_indices()));
                    self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@),
                                                        Ghost(self.overall_metadata));

                    proof {
                        assert(!self.transaction_committed());
                        lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                            old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata
                        );
                        self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();

                        // These assertions help us prove that the pending allocation inv is restored
                        let tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                            self.log@.commit_op_log().physical_op_list).unwrap();
                        let durable_main_table_region = extract_bytes(self.wrpm@.committed(), 
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        assert(self.wrpm@.committed() == tentative_state_bytes);
                        assert(main_table_subregion_view.can_crash_as(durable_main_table_region));
                    }

                    return Err(e);
                }
            }

            // Prove that the overall and version metadata was not modified by committing the log.
            assert({
                &&& deserialize_version_metadata(self.wrpm@.committed()) == self.version_metadata
                &&& deserialize_overall_metadata(self.wrpm@.committed(), self.version_metadata.overall_metadata_addr) == self.overall_metadata
            }) by {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).wrpm@, self.wrpm@, self.version_metadata, self.overall_metadata);
                assert(self.wrpm@.can_crash_as(self.wrpm@.committed()));
                assert(deserialize_version_metadata(self.wrpm@.committed()) == self.version_metadata);
                assert(deserialize_overall_metadata(self.wrpm@.committed(), self.version_metadata.overall_metadata_addr) == self.overall_metadata);
            }

            let ghost abstract_op_log = UntrustedOpLog::<K, L>::recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata).unwrap();

            // 3. Install the physical log
            proof {
                // First, prove various facts about what will happen if we install the log.

                let phys_log_view = PhysicalOpLogEntry::vec_view(self.pending_updates);
                let old_mem_with_log_installed = Self::apply_physical_log_entries(old(self).wrpm@.flush().committed(), phys_log_view).unwrap();
                let new_mem_with_log_installed = Self::apply_physical_log_entries(self.wrpm@.committed(), phys_log_view).unwrap();

                // Prove that the logged updates tracked in volatile memory constitute a valid log (which implies
                // replaying the log will succeed and result in a valid KV store state)
                assert(PhysicalOpLogEntry::log_inv(self.pending_updates, self.version_metadata, self.overall_metadata)) by {
                    PhysicalOpLogEntry::lemma_abstract_log_inv_implies_concrete_log_inv(self.pending_updates,
                        self.version_metadata, self.overall_metadata);
                }

                // If we replay the concrete log in volatile memory and the ghost log, the resulting bytes
                // in each non-log region will match
                assert(abstract_op_log.physical_op_list == phys_log_view);
                Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old(self).wrpm@.flush().committed(), self.wrpm@.committed(),
                    phys_log_view, self.version_metadata, self.overall_metadata);
                Self::lemma_log_replay_preserves_size(self.wrpm@.committed(), phys_log_view);
                assert(states_differ_only_in_log_region(old_mem_with_log_installed, new_mem_with_log_installed, 
                    self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old_mem_with_log_installed, new_mem_with_log_installed, self.version_metadata, self.overall_metadata);

                // If we replay the log, we will obtain the current tentative view
                assert(Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == old(self).tentative_view());
                // The post-install recovery state is allowed by `perm`
                assert(forall |s| Self::physical_recover(self.wrpm@.committed(), self.version_metadata, self.overall_metadata) == 
                    Self::physical_recover(s, self.version_metadata, self.overall_metadata) ==> perm.check_permission(s));
            }

            let ghost pre_log_install_wrpm = self.wrpm;

            Self::install_log(&mut self.wrpm, self.version_metadata, self.overall_metadata, &self.pending_updates, Tracked(perm));

            proof {
                // Some functions/proofs use `extract_bytes`  and some use `get_subregion_view` 
                // (depending on whether they need PersistentMemoryRegionView information or not)
                // so we first have to prove that these are equivalent.
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.wrpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.wrpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.wrpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);        
                            
                let subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(subregion_view.can_crash_as(subregion_view.committed()));

                let old_subregion_view = get_subregion_view(old(self).wrpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat); 
                assert(old_subregion_view.can_crash_as(old_subregion_view.committed()));
                assert(parse_main_table::<K>(old_subregion_view.committed(), self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) is Some);

                let tentative_bytes_main_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
            
                let durable_state_bytes = old(self).wrpm@.committed();
                let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(durable_main_table_region == old_subregion_view.committed());
                
            }

            // 4. Update ghost state and finalize pending (de)allocations.
            self.main_table.finalize_main_table(Ghost(old(self).main_table), Ghost(old(self).wrpm@),
                Ghost(self.wrpm@), Ghost(self.overall_metadata));
            self.item_table.finalize_item_table(Ghost(old(self).item_table), Ghost(self.wrpm@), 
                Ghost(self.overall_metadata), Ghost(old(self).main_table@.valid_item_indices()), Ghost(self.main_table@.valid_item_indices()));

            // TODO: replace with finalize fn that finishes (de)allocs and updates ghost state
            self.durable_list.update_ghost_state_to_current_bytes(Ghost(self.wrpm@), Ghost(self.overall_metadata), 
                Ghost(self.main_table@));

            // We now need a more restrictive crash predicate, as there are fewer legal crash states now that 
            // we have replayed the log. It's still the case that clear_log_crash_pred(s) ==> perm.check_permission(s)
            let ghost clear_log_crash_pred = |s: Seq<u8>| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@);

            // 5. Clear the log
            proof {
                // Next, prove that we can safely clear the log.
                self.lemma_can_clear_op_log_after_commit(*old(self), pre_log_install_wrpm, 
                    abstract_op_log, clear_log_crash_pred, &perm);

                let durable_item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat);
                let durable_list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                    self.overall_metadata.list_area_size as nat);
                
                // Establish some facts about the possible crash states of the item table and list area
                // to reestablish their invariants
                // The assertions and lemmas here seem redundant, but the assertions appear to have an impact on a later proof,
                // and the lemmas are required to reestablish the invariants.
                assert(durable_item_table_subregion_view.can_crash_as(durable_item_table_subregion_view.committed()));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_item_table_subregion_view);
                assert(durable_list_area_subregion_view.can_crash_as(durable_list_area_subregion_view.committed()));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_list_area_subregion_view);
            }
            
            let ghost pre_clear_wrpm = self.wrpm@;
            self.log.clear_log(&mut self.wrpm, self.version_metadata, self.overall_metadata, Ghost(clear_log_crash_pred), Tracked(perm))?;
            self.pending_updates = Vec::new();
            
            proof {
                // clearing the log does not change the view of any other parts of the KV store
                self.lemma_view_and_components_unchanged(pre_clear_wrpm);

                // The new durable and tentative states are equal.
                let new_durable_state_bytes = self.wrpm@.committed();
                let new_tentative_state_bytes = Self::apply_physical_log_entries(self.wrpm@.flush().committed(),
                    self.log@.commit_op_log().physical_op_list).unwrap();
                assert(new_durable_state_bytes == new_tentative_state_bytes);

                // The log and the local pending lists are both empty
                assert(self.log@.physical_op_list.len() == 0);
                assert(self.pending_updates@.len() == 0);
                assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);
                
                // Version and overall metadata remain the same in all current crash states.
                assert(no_outstanding_writes_to_version_metadata(self.wrpm@));
                assert(no_outstanding_writes_to_overall_metadata(self.wrpm@, self.version_metadata.overall_metadata_addr as int));
                assert(self.inv_mem(self.wrpm@.committed()));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(self.wrpm@);
                assert(forall |s| #[trigger] self.wrpm@.can_crash_as(s) ==> self.inv_mem(s));
            }
            
            Ok(())
        }

        proof fn lemma_view_and_components_unchanged(
            self,
            pre_state: PersistentMemoryRegionView,
        )
            requires 
                views_differ_only_in_log_region(self.wrpm@, pre_state, self.overall_metadata.log_area_addr as nat,
                    self.overall_metadata.log_area_size as nat),
                ({
                    let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(pre_durable_main_table_subregion_view.committed(), 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@)
                }),
                self.wrpm@.no_outstanding_writes(),
                pre_state.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr,
                    self.overall_metadata.kvstore_id),
                pre_state.len() == self.wrpm@.len(),
                self.wrpm@.len() == self.overall_metadata.region_size,
            ensures 
                ({
                    let durable_main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    let durable_item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                    let pre_durable_item_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                    let durable_list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                        self.overall_metadata.list_area_size as nat);
                    let pre_durable_list_area_subregion_view = get_subregion_view(pre_state, self.overall_metadata.list_area_addr as nat,
                        self.overall_metadata.list_area_size as nat);
                    &&& pre_durable_main_table_subregion_view.state == durable_main_table_subregion_view.state
                    &&& pre_durable_item_table_subregion_view.state == durable_item_table_subregion_view.state
                    &&& pre_durable_list_area_subregion_view.state == durable_list_area_subregion_view.state
                    &&& durable_main_table_subregion_view.can_crash_as(pre_durable_main_table_subregion_view.committed())
                    &&& forall |s| #[trigger] durable_main_table_subregion_view.can_crash_as(s) ==> parse_main_table::<K>(s, self.overall_metadata.num_keys, 
                            self.overall_metadata.main_table_entry_size) == Some(self.main_table@)
                }),
                extracted_regions_match(self.wrpm@.committed(), pre_state.committed(), self.overall_metadata),
                deserialize_version_metadata(self.wrpm@.committed()) == deserialize_version_metadata(pre_state.committed()),
                deserialize_overall_metadata(self.wrpm@.committed(), self.version_metadata.overall_metadata_addr) == 
                        deserialize_overall_metadata(pre_state.committed(), self.version_metadata.overall_metadata_addr),

        {
            let durable_main_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);
            let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);
            let durable_item_table_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat);
            let pre_durable_item_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat);
            let durable_list_area_subregion_view = get_subregion_view(self.wrpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);
            let pre_durable_list_area_subregion_view = get_subregion_view(pre_state, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(pre_state.committed(),
                self.wrpm@.committed(), self.version_metadata, self.overall_metadata);

            assert(pre_durable_main_table_subregion_view.state == durable_main_table_subregion_view.state);
            assert(pre_durable_item_table_subregion_view.state == durable_item_table_subregion_view.state);
            assert(pre_durable_list_area_subregion_view.state == durable_list_area_subregion_view.state);
        
            assert(durable_main_table_subregion_view.can_crash_as(pre_durable_main_table_subregion_view.committed()));
            lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_main_table_subregion_view);
            assert(forall |s| #[trigger] durable_main_table_subregion_view.can_crash_as(s) ==> parse_main_table::<K>(s, 
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@));
        }
    }     
}
