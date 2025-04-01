//! This file contains a trait that defines the interface for the high-level
//! durable component of the KV store.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::assert_seqs_equal;
use vstd::bytes::u64_from_le_bytes;
use vstd::bytes::u64_to_le_bytes;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

use crate::kv::durable::commonlayout_v::*;
use crate::kv::durable::inv_v::*;
use crate::kv::durable::list_v::*;
use crate::kv::durable::listlayout_v::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::durable::itemtable_v::*;
use crate::kv::durable::itemtablelayout_v::*;
use crate::kv::durable::maintable_v::*;
use crate::kv::durable::maintablelayout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::recovery_v::*;
use crate::kv::durable::util_v::*;
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
use crate::pmem::pmemutil_v::*;
use crate::pmem::power_t::*;
use crate::pmem::subregion_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t;
use crate::pmem::power_t::*;
use crate::pmem::pmemutil_v::*;
use crate::common::util_v::*;
use std::borrow::Borrow;
use std::hash::Hash;

use super::inv_v::*;

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
        K: PmCopy + Hash + Eq,
    {
        pub key: K,
        pub item: I,
        pub list: DurableKvStoreList<L>,

    }

    // TODO: remove since the fields are public
    impl<K, I, L> DurableKvStoreViewEntry<K, I, L>
    where
        K: PmCopy + Hash + Eq,
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

    #[verifier::ext_equal]
    pub struct DurableKvStoreView<K, I, L>
    where
        K: PmCopy + Hash + Eq + std::fmt::Debug,
    {
        pub contents: Map<int, DurableKvStoreViewEntry<K, I, L>>,
    }

    impl<K, I, L> DurableKvStoreView<K, I, L>
    where
        K: PmCopy + Hash + Eq + std::fmt::Debug,
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
    }

    #[verifier::reject_recursive_types(K)]
    #[verifier::reject_recursive_types(I)]
    pub struct DurableKvStore<Perm, PM, K, I, L>
    where
        Perm: CheckPermission<Seq<u8>>,
        PM: PersistentMemoryRegion,
        K: PmCopy + Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
        I: PmCopy + Sized + std::fmt::Debug,
        L: PmCopy + std::fmt::Debug,
    {
        version_metadata: VersionMetadata,
        overall_metadata: OverallMetadata,
        item_table: DurableItemTable<K, I>,
        durable_list: DurableList<K, L>,
        log: UntrustedOpLog<K, L>,
        main_table: MainTable<K>,
        powerpm: PoWERPersistentMemoryRegion<Perm, PM>,
        pending_updates: Vec<PhysicalOpLogEntry>,
    }

    impl<Perm, PM, K, I, L> DurableKvStore<Perm, PM, K, I, L>
        where
            PM: PersistentMemoryRegion,
            Perm: CheckPermission<Seq<u8>>,
            K: PmCopy + Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
    {
        pub closed spec fn view(&self) -> DurableKvStoreView<K, I, L>
        {
            Self::recover_from_component_views(self.main_table@, self.item_table@)
        }

        pub closed spec fn key_index_list_view(self) -> Set<(K, u64, u64)>
        {
            Set::new(
                |val: (K, u64, u64)| {
                    exists |j: u64| {
                        &&& 0 <= j < self.main_table@.durable_main_table.len()
                        &&& #[trigger] self.main_table@.durable_main_table[j as int] matches Some(entry)
                        &&& val == (entry.key(), j, entry.item_index())
            }})
        }

        pub closed spec fn tentative_view(self) -> Option<DurableKvStoreView<K, I, L>>
        {
            Self::physical_recover_after_committing_log(self.powerpm@.read_state, self.overall_metadata, self.log@)
        }

        pub closed spec fn tentative_main_table_valid(self) -> bool
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_main_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let tentative_main_table =
                parse_main_table::<K>(tentative_main_table_bytes, self.overall_metadata.num_keys,
                                      self.overall_metadata.main_table_entry_size);
            &&& tentative_state_bytes is Some
            &&& tentative_main_table is Some
        }

        pub closed spec fn tentative_main_table(self) -> MainTableView<K>
            recommends
                self.tentative_main_table_valid()
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_main_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let tentative_main_table =
                parse_main_table::<K>(tentative_main_table_bytes, self.overall_metadata.num_keys,
                                      self.overall_metadata.main_table_entry_size);
            tentative_main_table.unwrap()
        }

        pub closed spec fn tentative_item_table_valid(self) -> bool
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_main_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let tentative_item_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let tentative_main_table =
                parse_main_table::<K>(tentative_main_table_bytes, self.overall_metadata.num_keys,
                                      self.overall_metadata.main_table_entry_size);
            let tentative_item_table =
                parse_item_table::<I, K>(tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         tentative_main_table.unwrap().valid_item_indices());
            &&& tentative_state_bytes is Some
            &&& tentative_main_table is Some
            &&& tentative_item_table is Some
        }
        
        pub closed spec fn tentative_item_table(self) -> DurableItemTableView<I>
            recommends
                self.tentative_item_table_valid()
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_main_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let tentative_item_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let tentative_main_table =
                parse_main_table::<K>(tentative_main_table_bytes, self.overall_metadata.num_keys,
                                      self.overall_metadata.main_table_entry_size);
            let tentative_item_table =
                parse_item_table::<I, K>(tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         tentative_main_table.unwrap().valid_item_indices());
            tentative_item_table.unwrap()
        }

        pub closed spec fn tentative_hypothetical_item_table_valid(self, hypothetical_item_indices: Set<u64>) -> bool
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_item_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let tentative_item_table =
                parse_item_table::<I, K>(tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         hypothetical_item_indices);
            &&& tentative_state_bytes is Some
            &&& tentative_item_table is Some
        }
        
        pub closed spec fn tentative_hypothetical_item_table(self, hypothetical_item_indices: Set<u64>)
                                                             -> DurableItemTableView<I>
            recommends
                self.tentative_hypothetical_item_table_valid(hypothetical_item_indices)
        {
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list);
            let tentative_item_table_bytes =
                extract_bytes(tentative_state_bytes.unwrap(), self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let tentative_item_table =
                parse_item_table::<I, K>(tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         hypothetical_item_indices);
            tentative_item_table.unwrap()
        }

        pub closed spec fn constants(self) -> PersistentMemoryConstants
        {
            self.powerpm.constants()
        }

        pub closed spec fn inv_mem(self, mem: Seq<u8>) -> bool
        {
            &&& self.version_metadata == deserialize_version_metadata(mem)
            &&& self.overall_metadata == deserialize_overall_metadata(mem, self.version_metadata.overall_metadata_addr)
            &&& Self::physical_recover(mem, self.version_metadata, self.overall_metadata) == Some(self@)
        }

        pub closed spec fn inv(self) -> bool 
        {
            let pm_view = self.powerpm@;
            &&& self.powerpm.inv()
            &&& overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr)
            &&& self.powerpm@.len() == self.overall_metadata.region_size
            &&& self.log.inv(pm_view, self.version_metadata, self.overall_metadata)
            &&& no_outstanding_writes_to_version_metadata(self.powerpm@)
            &&& no_outstanding_writes_to_overall_metadata(self.powerpm@, self.version_metadata.overall_metadata_addr as int)
            &&& self.inv_mem(pm_view.durable_state)
            &&& self.version_metadata == deserialize_version_metadata(pm_view.read_state)
            &&& self.overall_metadata == deserialize_overall_metadata(pm_view.read_state,
                                                                    self.version_metadata.overall_metadata_addr)
            &&& self.main_table.inv(get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat),
                                  self.overall_metadata)
            &&& self.item_table.inv(get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                                     self.overall_metadata.item_table_size as nat), self.overall_metadata)
            /* REMOVED UNTIL WE IMPLEMENT LISTS
            &&& self.durable_list.inv(get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                                       self.overall_metadata.list_area_size as nat),
                                    self.main_table@, self.overall_metadata)
            */
            &&& PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list
            &&& log_entries_do_not_modify_item_table(self.log@.physical_op_list, self.overall_metadata)
            &&& log_entries_do_not_modify_free_main_table_entries(self.log@.physical_op_list,
                                                                self.main_table.free_indices(),
                                                                self.overall_metadata)
            &&& self.tentative_view() is Some
            &&& self.tentative_main_table_valid()
            &&& self.tentative_item_table_valid()
        }

        // This invariant relates the main table and item table's own tentative views
        // to those obtained from tentative_main_table() and tentative_item_table(). 
        // It also ensures that the sets of valid item indices for the durable and 
        // and tentative states match. This invariant is part of valid() but not inv()
        // because it may be broken during a tentative operation.
        pub closed spec fn tentative_view_inv(self) -> bool 
        {
            &&& self.tentative_main_table() == self.main_table.tentative_view()
            &&& self.tentative_item_table() == self.item_table.tentative_view()
            &&& forall |i: int| self.tentative_view().unwrap().contains_key(i) ==> i < self.overall_metadata.num_keys

            &&& self.main_table.tentative_view().valid_item_indices() == self.item_table.tentative_valid_indices()
            &&& self.main_table@.valid_item_indices() == self.item_table.durable_valid_indices()
        }

        pub closed spec fn valid(self) -> bool 
        {
            let pm_view = self.powerpm@;
            &&& self.inv()
            &&& self.main_table.valid(get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                                                       self.overall_metadata.main_table_size as nat),
                                    self.overall_metadata)
            &&& self.item_table.valid(get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata,
                                    self.main_table@.valid_item_indices())
            &&& self.tentative_view_inv()
        }

        pub proof fn lemma_reveal_opaque_inv(self)
            requires 
                self.inv(),
            ensures 
                Self::physical_recover(self.powerpm_view().durable_state, self.spec_version_metadata(), 
                                       self.spec_overall_metadata()) == Some(self@),
                self.spec_version_metadata() == deserialize_version_metadata(self.powerpm_view().durable_state),
                self.spec_version_metadata() == deserialize_version_metadata(self.powerpm_view().read_state),
                self.spec_overall_metadata() ==
                    deserialize_overall_metadata(self.powerpm_view().durable_state, 
                                                 self.spec_version_metadata().overall_metadata_addr),
                self.spec_overall_metadata() ==
                    deserialize_overall_metadata(self.powerpm_view().read_state,
                                                 self.spec_version_metadata().overall_metadata_addr),
                no_outstanding_writes_to_version_metadata(self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(self.powerpm_view(), self.spec_overall_metadata_addr() as int),
                self.inv_mem(self.powerpm_view().durable_state),
                self.tentative_view() is Some,
                self.powerpm_view().len() == self.spec_overall_metadata().region_size,
                self.powerpm_view().len() >= VersionMetadata::spec_size_of(),
        {
//            assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));
        }

        pub proof fn lemma_reveal_opaque_inv_mem(self)
            requires
                self.inv_mem(self.powerpm_view().durable_state),
            ensures 
                ({
                    let s = self.powerpm_view().durable_state;
                    &&& self.spec_version_metadata() == deserialize_version_metadata(s)
                    &&& self.spec_overall_metadata() == deserialize_overall_metadata(s, self.spec_version_metadata().overall_metadata_addr)
                    &&& Self::physical_recover(s, self.spec_version_metadata(), self.spec_overall_metadata()) == Some(self@)
                }),
        {}

        pub proof fn lemma_overall_metadata_addr(self) 
            ensures
                self.spec_version_metadata().overall_metadata_addr == 
                    self.spec_overall_metadata_addr()
        {}

        pub proof fn lemma_valid_implies_inv(self) 
            requires 
                self.valid()
            ensures
                self.inv(),
                self.tentative_view_inv(),
        {}

        pub closed spec fn transaction_committed(self) -> bool
        {
            self.log@.op_list_committed
        }

        pub closed spec fn powerpm_view(self) -> PersistentMemoryRegionView
        {
            self.powerpm@
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

        pub exec fn num_log_entries_in_current_transaction(&self) -> (out: usize)
            requires 
                self.valid(),
            ensures 
                out == self.spec_num_log_entries_in_current_transaction()
        {
            self.pending_updates.len()
        }

        // In physical recovery, we blindly replay the physical log obtained by recovering the op log onto the rest of the
        // persistent memory region.
        pub open spec fn physical_recover(mem: Seq<u8>, version_metadata: VersionMetadata, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>> {
            if mem.len() != overall_metadata.region_size {
                None
            } else if !overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr) {
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
            let mem_with_log_installed = apply_physical_log_entries(mem, physical_log_entries);
            if let Some(mem_with_log_installed) = mem_with_log_installed {
                Self::physical_recover_after_applying_log(mem_with_log_installed, overall_metadata)
            } else {
                None
            }
        }

        pub open spec fn physical_recover_after_applying_log(mem_with_log_installed: Seq<u8>, overall_metadata: OverallMetadata) -> Option<DurableKvStoreView<K, I, L>>
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
                    /* REMOVED UNTIL WE IMPLEMENT LISTS
                    let list_view = DurableList::<K, L>::parse_all_lists(
                        main_table_view,
                        list_area_region,
                        overall_metadata.list_node_size,
                        overall_metadata.num_list_entries_per_node
                    );
                    */
                    Some(Self::recover_from_component_views(main_table_view, item_table_view))
                } else { 
                    None
                }
            } else {
                None
            }
        }

        proof fn lemma_index_in_tentative_view_is_also_in_main_table_tentative_view(self, metadata_index: u64) 
            requires 
                self.valid(),
                self.tentative_view() is Some,
                self.tentative_view().unwrap().contains_key(metadata_index as int),
            ensures 
                self.tentative_main_table().durable_main_table[metadata_index as int] is Some 
        {}

        proof fn lemma_tentative_view_matches_durable_when_log_is_empty(self)
            requires 
                self.log@.physical_op_list.len() == 0,
                self.powerpm@.flush_predicted(),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) ==
                    Some(self@),
                UntrustedOpLog::<K, L>::recover(self.powerpm@.read_state, self.version_metadata, self.overall_metadata) ==
                    Some(self.log@),
            ensures 
                Some(self@) == self.tentative_view()
        {
            assert(Some(self@) == self.tentative_view());
        }

        // This lemma proves that after `tentatively_append_log_entry` fails and begins to abort the 
        // current transaction, replaying the log is a no op and we can still recover to a valid state.
        // This satisfies the preconditions for the individual components' abort functions, which
        // will reestablish their invariants before returning an error to the caller.
        proof fn lemma_transaction_abort(self, old_self: Self)
            requires
                old_self.inv(),
                self.overall_metadata == old_self.overall_metadata,
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.powerpm@.len() >= VersionMetadata::spec_size_of(),
                !old_self.transaction_committed(),
                self.powerpm@.len() == old_self.powerpm@.len(),
                self.powerpm@.flush_predicted(),
                0 < self.version_metadata.overall_metadata_addr < 
                    self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() <
                    self.overall_metadata.log_area_addr,
                0 < VersionMetadata::spec_size_of() <
                    self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() < self.powerpm@.len(),
                Self::physical_recover(old_self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) ==
                    Some(old_self@),
                UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata,
                                                self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                views_differ_only_in_log_region(old_self.powerpm@, self.powerpm@,
                                                self.overall_metadata.log_area_addr as nat,
                                                self.overall_metadata.log_area_size as nat),
                old_self.main_table@.valid_item_indices() == self.main_table@.valid_item_indices(),
                old_self.item_table.durable_valid_indices() == old_self.main_table@.valid_item_indices(),
            ensures
                ({
                    let main_table_subregion_view =
                        get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                           self.overall_metadata.main_table_size as nat);      
                    &&& parse_main_table::<K>(main_table_subregion_view.durable_state,
                                            self.overall_metadata.num_keys,
                                            self.overall_metadata.main_table_entry_size) == Some(old_self.main_table@)
                }),
                ({
                    let old_item_table_subregion_view =
                        get_subregion_view(old_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                           self.overall_metadata.item_table_size as nat); 
                    let item_table_subregion_view =
                        get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                           self.overall_metadata.item_table_size as nat);      
                    &&& parse_item_table::<I, K>(item_table_subregion_view.durable_state,
                                                self.overall_metadata.num_keys as nat,
                                                self.main_table@.valid_item_indices())
                        == Some(old_self.item_table@)
                }),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) is Some,
        {
            old_self.powerpm.lemma_inv_implies_view_valid();
            let main_table_subregion_view =
                get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat);      
            let item_table_subregion_view =
                get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                   self.overall_metadata.item_table_size as nat); 
            let list_area_subregion_view =
                get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                   self.overall_metadata.list_area_size as nat);
    
            let old_main_table_subregion_view =
                get_subregion_view(old_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat);      
            let old_item_table_subregion_view =
                get_subregion_view(old_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                   self.overall_metadata.item_table_size as nat); 
            let old_list_area_subregion_view =
                get_subregion_view(old_self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                   self.overall_metadata.list_area_size as nat);
    
            let recovered_op_log = UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata,
                                                                   self.overall_metadata).unwrap();
            let mem_with_log_installed = apply_physical_log_entries(self.powerpm@.durable_state,
                                                                    recovered_op_log.physical_op_list).unwrap();
            let main_table_region_view_with_log_installed =
                extract_bytes(mem_with_log_installed, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);   
            let item_table_region_view_with_log_installed =
                extract_bytes(mem_with_log_installed, self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat); 
            let list_area_region_view_with_log_installed =
                extract_bytes(mem_with_log_installed, self.overall_metadata.list_area_addr as nat,
                              self.overall_metadata.list_area_size as nat); 
            assert(main_table_region_view_with_log_installed == main_table_subregion_view.durable_state);
            assert(item_table_region_view_with_log_installed == item_table_subregion_view.durable_state);
            assert(list_area_region_view_with_log_installed == list_area_subregion_view.durable_state);

            /*
            lemma_if_views_differ_only_in_region_then_states_do(old_self.powerpm@, self.powerpm@,
                                                                self.overall_metadata.log_area_addr as nat,
                                                                self.overall_metadata.log_area_size as nat);
            */
            assert(main_table_subregion_view =~= old_main_table_subregion_view);
            assert(item_table_subregion_view =~= old_item_table_subregion_view);

            assert(parse_main_table::<K>(main_table_subregion_view.durable_state, self.overall_metadata.num_keys,
                                         self.overall_metadata.main_table_entry_size) == Some(old_self.main_table@));
            assert(forall |idx: u64| old_self.main_table.free_list().contains(idx) ==> idx < self.overall_metadata.num_keys);

            assert(Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata)
                   is Some);
            lemma_physical_recover_succeeds_implies_component_parse_succeeds::<Perm, PM, K, I, L>(
                self.powerpm@.durable_state, self.version_metadata, self.overall_metadata
            );
        }

        pub proof fn lemma_metadata_unchanged_when_views_differ_only_in_log_region(
            v1: PersistentMemoryRegionView,
            v2: PersistentMemoryRegionView,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
        )
            requires
                v1.valid(),
                v2.valid(),
                views_differ_only_in_log_region(v1, v2, overall_metadata.log_area_addr as nat,
                                                overall_metadata.log_area_size as nat),
                version_metadata == deserialize_version_metadata(v1.durable_state),
                version_metadata.spec_crc() == deserialize_version_crc(v1.durable_state),
                overall_metadata == deserialize_overall_metadata(v1.durable_state, version_metadata.overall_metadata_addr),
                overall_metadata.spec_crc() == deserialize_overall_crc(v1.durable_state, version_metadata.overall_metadata_addr),
                v2.flush_predicted(),
                no_outstanding_writes_to_version_metadata(v1),
                no_outstanding_writes_to_overall_metadata(v1, version_metadata.overall_metadata_addr as int),
                0 < version_metadata.overall_metadata_addr < 
                    version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of() <=
                    overall_metadata.log_area_addr,
                0 < VersionMetadata::spec_size_of() < version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of() < v1.len(),
                v1.len() == v2.len(),
                v1.len() >= VersionMetadata::spec_size_of(),
                v1.len() == overall_metadata.region_size,
            ensures 
                version_metadata == deserialize_version_metadata(v2.durable_state),
                version_metadata.spec_crc() == deserialize_version_crc(v2.durable_state),
                overall_metadata == deserialize_overall_metadata(v2.durable_state, version_metadata.overall_metadata_addr),
                overall_metadata.spec_crc() == deserialize_overall_crc(v2.durable_state, version_metadata.overall_metadata_addr),
        {
            lemma_establish_extract_bytes_equivalence(v1.durable_state, v2.durable_state);
            lemma_establish_extract_bytes_equivalence(v1.read_state, v2.durable_state);
//            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(v1);

            assert(version_metadata == deserialize_version_metadata(v1.durable_state));
            assert(overall_metadata == deserialize_overall_metadata(v1.durable_state, version_metadata.overall_metadata_addr));
            assert(overall_metadata.spec_crc() == deserialize_overall_crc(v1.durable_state, version_metadata.overall_metadata_addr));

            assert(extract_version_metadata(v1.durable_state) == extract_version_metadata(v2.durable_state));
            assert(extract_overall_metadata(v1.durable_state, version_metadata.overall_metadata_addr) == 
                extract_overall_metadata(v2.durable_state, version_metadata.overall_metadata_addr));
                
            assert(extract_overall_crc(v1.durable_state, version_metadata.overall_metadata_addr) == 
                extract_overall_crc(v2.durable_state, version_metadata.overall_metadata_addr));

            assert(version_metadata == deserialize_version_metadata(v1.read_state));
            assert(overall_metadata == deserialize_overall_metadata(v1.read_state, version_metadata.overall_metadata_addr));
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
                    let mem1_with_log = apply_physical_log_entries(mem1, op_log);
                    let mem2_with_log = apply_physical_log_entries(mem2, op_log);
                    &&& mem1_with_log matches Some(mem1_with_log)
                    &&& mem2_with_log matches Some(mem2_with_log)
                    &&& states_differ_only_in_log_region(mem1_with_log, mem2_with_log, overall_metadata.log_area_addr as nat,
                            overall_metadata.log_area_size as nat)
                })
        {
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(mem1, version_metadata, overall_metadata, op_log);
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(mem2, version_metadata, overall_metadata, op_log);
            lemma_log_replay_preserves_size(mem1, op_log);
            lemma_log_replay_preserves_size(mem2, op_log);


            let mem1_with_log = apply_physical_log_entries(mem1, op_log).unwrap();
            let mem2_with_log = apply_physical_log_entries(mem2, op_log).unwrap();

            assert forall |addr: int| {
                &&& 0 <= addr < mem1.len() 
                &&& !(overall_metadata.log_area_addr <= addr < overall_metadata.log_area_addr + overall_metadata.log_area_size)
            } implies mem1_with_log[addr] == #[trigger] mem2_with_log[addr] by {
                lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, op_log);
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
                perm.check_permission(self.powerpm@.durable_state),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@),
                forall |s| {
                    &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                } ==> #[trigger] perm.check_permission(s),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@),
                no_outstanding_writes_to_version_metadata(self.powerpm@),
                no_outstanding_writes_to_overall_metadata(self.powerpm@, self.version_metadata.overall_metadata_addr as int),
                self.powerpm@.len() >= VersionMetadata::spec_size_of(),
                apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list) is Some,
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s| {
                    &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                } <==> #[trigger] crash_pred(s),
            ensures
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                } ==> #[trigger] crash_pred(s2),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                        UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
    
        {
            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
    
            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

            assert(Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@) ==>
                    UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()))
            by {
                self.log.lemma_if_not_committed_recovery_equals_drop_pending_appends(self.powerpm, self.version_metadata, self.overall_metadata);
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
                let mem_with_log_installed_s1 = apply_physical_log_entries(s1, recovered_log.physical_op_list).unwrap();
                assert(mem_with_log_installed_s1 == s1);
                let mem_with_log_installed_s2 = apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
                assert(mem_with_log_installed_s2 == s2);

                lemma_establish_extract_bytes_equivalence(s1, s2);
                
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    mem_with_log_installed_s1, mem_with_log_installed_s2, self.version_metadata, self.overall_metadata);
    
                assert(Self::physical_recover(s1, self.version_metadata, self.overall_metadata) == Some(self@));
                assert(Self::physical_recover(s2, self.version_metadata, self.overall_metadata) == Some(self@));
            }
        }

        // This has to be callable during `start` when we don't have a DurableKvStore yet,
        // so it cannot take a `self` argument.
        proof fn lemma_clear_log_is_crash_safe(
            powerpm_region: PoWERPersistentMemoryRegion<Perm, PM>,
            op_log: UntrustedOpLog<K, L>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            state: DurableKvStoreView<K, I, L>,
            perm: &Perm
        )
            requires 
                op_log.inv(powerpm_region@, version_metadata, overall_metadata),
                op_log@.op_list_committed,
                perm.check_permission(powerpm_region@.durable_state),
                UntrustedOpLog::<K, L>::recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(op_log@),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state),
                powerpm_region@.flush_predicted(),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s| {
                    &&& Self::physical_recover(s, version_metadata, overall_metadata) == Some(state)
                    &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
                } <==> #[trigger] crash_pred(s),
                powerpm_region@.len() >= VersionMetadata::spec_size_of(),
                overall_metadata.list_area_addr + overall_metadata.list_area_size <= powerpm_region@.len(),
                powerpm_region@.len() == overall_metadata.region_size,
                AbstractPhysicalOpLogEntry::log_inv(op_log@.physical_op_list, version_metadata, overall_metadata),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == 
                    Self::physical_recover_given_log(powerpm_region@.durable_state, overall_metadata, AbstractOpLogState::initialize()),
                deserialize_version_metadata(powerpm_region@.durable_state) == version_metadata,
            ensures 
                forall |s2: Seq<u8>| {
                    let current_state = powerpm_region@.read_state;
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
            assert(Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state) ==> {
                    ||| UntrustedOpLog::<K, L>::recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(op_log@)
                    ||| UntrustedOpLog::<K, L>::recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                });

            Self::lemma_clear_log_is_crash_safe_case1(powerpm_region, op_log, version_metadata, overall_metadata, crash_pred, state, perm);

            // case 2
            assert forall |s1: Seq<u8>, s2: Seq<u8>| {
                &&& s1.len() == s2.len() 
                &&& #[trigger] crash_pred(s1)
                &&& states_differ_only_in_log_region(s1, s2, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                &&& UntrustedOpLog::<K, L>::recover(s1, version_metadata, overall_metadata) == Some(op_log@)
                &&& UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
            } implies #[trigger] crash_pred(s2) by {
                // In this case, the log was not durably cleared before the crash, so the log recovers to its old state
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s1, version_metadata, overall_metadata, op_log@.physical_op_list);
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(s2, version_metadata, overall_metadata, op_log@.physical_op_list);
                lemma_log_replay_preserves_size(s1, op_log@.physical_op_list);
                lemma_log_replay_preserves_size(s2, op_log@.physical_op_list);
                lemma_establish_extract_bytes_equivalence(s1, s2);

                // For this crash pre condition, we'll prove that recovering from s1_with_log_installed's non-log components plus op_log (which we already 
                // know is the recovery state of its op log) is equivalent to recovering normally from s1 (which we already know, from crash_pred(s1), gives
                // Some(state)). Then, we prove that s2 has the same non-log components after replaying op_log (which we already know is also the recovery state
                // of its op log) as s1, which tells us that they recover to the same DurableKvStore state.
                let s1_with_log_installed = apply_physical_log_entries(s1, op_log@.physical_op_list).unwrap();
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
                /* REMOVED UNTIL WE IMPLEMENT LISTS
                let list_view = DurableList::<K, L>::parse_all_lists(
                    main_table_view,
                    list_area_region,
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node
                ).unwrap();
                */
                assert(Some(Self::recover_from_component_views(main_table_view, item_table_view)) == 
                    Self::physical_recover(s1, version_metadata, overall_metadata));
                let s2_with_log_installed = apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                    s1, s2, op_log@.physical_op_list, version_metadata, overall_metadata);
                let s2_with_log_installed = apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    s1_with_log_installed, s2_with_log_installed, version_metadata, overall_metadata);
                assert(Some(Self::recover_from_component_views(main_table_view, item_table_view)) == 
                    Self::physical_recover(s2, version_metadata, overall_metadata));
            }
        }

        proof fn lemma_clear_log_is_crash_safe_case1(
            powerpm_region: PoWERPersistentMemoryRegion<Perm, PM>,
            op_log: UntrustedOpLog<K, L>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            state: DurableKvStoreView<K, I, L>,
            perm: &Perm
        )
            requires 
                op_log.inv(powerpm_region@, version_metadata, overall_metadata),
                op_log@.op_list_committed,
                perm.check_permission(powerpm_region@.durable_state),
                UntrustedOpLog::<K, L>::recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(op_log@),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state),
                powerpm_region@.flush_predicted(),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s| {
                    &&& Self::physical_recover(s, version_metadata, overall_metadata) == Some(state)
                    &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
                } <==> #[trigger] crash_pred(s),
                powerpm_region@.len() >= VersionMetadata::spec_size_of(),
                overall_metadata.list_area_addr + overall_metadata.list_area_size <= powerpm_region@.len(),
                powerpm_region@.len() == overall_metadata.region_size,
                AbstractPhysicalOpLogEntry::log_inv(op_log@.physical_op_list, version_metadata, overall_metadata),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == 
                    Self::physical_recover_given_log(powerpm_region@.durable_state, overall_metadata, AbstractOpLogState::initialize()),
                deserialize_version_metadata(powerpm_region@.durable_state) == version_metadata,
            ensures 
                forall |s2: Seq<u8>| {
                    let current_state = powerpm_region@.read_state;
                    &&& current_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(s2, current_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                    &&& {
                            ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
                            ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                        }
                } ==> #[trigger] crash_pred(s2),
        {
            assert forall |s2: Seq<u8>| {
                let current_state = powerpm_region@.read_state;
                &&& current_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(s2, current_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                &&& {
                        ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@)
                        ||| UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize())
                    }
            } implies #[trigger] crash_pred(s2) by {
                let current_state = powerpm_region@.read_state;
//                lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(powerpm_region@);
//                assert(powerpm_region@.can_crash_as(current_state));
                lemma_establish_extract_bytes_equivalence(s2, current_state);

                if UntrustedOpLog::<K, L>::recover(s2, version_metadata, overall_metadata) == Some(op_log@) {
                    // The clear log op did not complete before the crash. In this case, we recover the full log  
                    Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                        current_state, s2, op_log@.physical_op_list, version_metadata, overall_metadata);
                    let current_state_with_log_installed = apply_physical_log_entries(current_state, op_log@.physical_op_list).unwrap();
                    let s2_with_log_installed = apply_physical_log_entries(s2, op_log@.physical_op_list).unwrap();
                    lemma_log_replay_preserves_size(current_state, op_log@.physical_op_list);
                    lemma_log_replay_preserves_size(s2, op_log@.physical_op_list);

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
                    let current_state_with_log_installed = apply_physical_log_entries(current_state, recovered_log.physical_op_list).unwrap();
                    assert(current_state_with_log_installed == current_state);
                    let s2_with_log_installed = apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
                    assert(s2_with_log_installed == s2);
                    lemma_log_replay_preserves_size(current_state, recovered_log.physical_op_list);
                    lemma_log_replay_preserves_size(s2, recovered_log.physical_op_list);

                    assert(states_differ_only_in_log_region(current_state_with_log_installed, s2_with_log_installed, 
                        overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        current_state_with_log_installed, s2_with_log_installed, version_metadata, overall_metadata);
                }
            }
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
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@),
                s1.len() == s2.len(),
                crash_pred(s1),
                states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat,
                    self.overall_metadata.log_area_size as nat),
                UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize()),
                forall |s|{
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                    &&& {
                        ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                        ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == self.tentative_view()
                    }
                } <==> #[trigger] crash_pred(s),
                no_outstanding_writes_to_version_metadata(self.powerpm@),
                no_outstanding_writes_to_overall_metadata(self.powerpm@, self.version_metadata.overall_metadata_addr as int),
                self.powerpm@.len() >= VersionMetadata::spec_size_of(),
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
            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();
            lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

            let recovered_log = AbstractOpLogState::initialize();
            let mem_with_log_installed_s1 = apply_physical_log_entries(s1, recovered_log.physical_op_list).unwrap();
            assert(mem_with_log_installed_s1 == s1);
            let mem_with_log_installed_s2 = apply_physical_log_entries(s2, recovered_log.physical_op_list).unwrap();
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

        // Note: this fn assumes that the item and list head in the main table entry point 
        // to valid entries in the corresponding structures.
        pub open spec fn recover_from_component_views(
            recovered_main_table: MainTableView<K>, 
            recovered_item_table: DurableItemTableView<I>,
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
                        /* REMOVED UNTIL WE IMPLEMENT LISTS
                    let list_view = recovered_lists.durable_lists[key];
                    let list = DurableKvStoreList {
                            list: Seq::new(
                                    list_view.len(),
                                    |i: int| list_view[i].unwrap_valid().list_element()
                                )
                    };
                        */
                    let list = DurableKvStoreList{ list: Seq::<L>::empty() };
                    DurableKvStoreViewEntry { key, item, list }
                }
            );
            DurableKvStoreView { contents }
        }

        proof fn lemma_if_key_missing_from_tentative_view_then_missing_from_tentative_main_table(self, key: K)
            requires
                self.tentative_view() is Some,
                forall|e| #[trigger] self.tentative_view().unwrap().contents.contains_value(e) ==> e.key != key,
            ensures
                self.tentative_main_table_valid(),
                ({
                    let t = self.tentative_main_table().durable_main_table;
                    forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Some ==> t[i].unwrap().key != key
                })
        {
            let v = self.tentative_view().unwrap();
            let t = self.tentative_main_table().durable_main_table;
            assert forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Some implies t[i].unwrap().key != key by {
                if t[i].unwrap().key == key {
                    assert(v.contents.contains_key(i));
                    assert(v.contents[i].key == key);
                    assert(v.contents.dom().contains(i));
                    assert(v.contents.contains_value(v.contents[i]));
                    assert(false);
                }
            }
        }

        pub exec fn get_elements_per_node(&self) -> u64 {
            self.durable_list.get_elements_per_node()
        }

        // This lemma establishes the relationship between the key_to_index map used 
        // to construct an abstract KV store view from durable state and the contents
        // of that durable state. This is very useful in proofs about the contents 
        // of the durable store vs. the overall kv store.
        // NOTE: this lemma only applies to DURABLE state, not tentative state stored in
        // volatile memory
        pub proof fn lemma_main_table_index_key_durable(self)
            requires 
                self.inv(),
                self.tentative_view_inv(),
            ensures 
                ({
                    let index_to_key = Map::new(
                        |i: int| self@.contents.dom().contains(i),
                        |i: int| self@.contents[i].key
                    );
                    let key_to_index = index_to_key.invert();
                    &&& forall |k| #[trigger] key_to_index.contains_key(k) ==> {
                            let index = key_to_index[k];
                            &&& self@.contains_key(index)
                            &&& self@.contents[index].key() == k
                        }
                    &&& index_to_key.is_injective()
                })
        {
            let index_to_key =  Map::new(
                |i: int| self@.contents.dom().contains(i),
                |i: int| self@.contents[i].key
            );
            // Prove that there are no duplicate keys in the main table; this implies that index_to_key 
            // in injective, which is crucial for the rest of the proof.
            let main_table_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat, 
                self.overall_metadata.main_table_size as nat);
            assert(parse_main_table::<K>(main_table_subregion.durable_state, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@));
//            assert(main_table_subregion.can_crash_as(main_table_subregion.durable_state));
            assert(no_duplicate_keys(self.main_table@.durable_main_table));

            // key_to_index is also injective since the inverse of a map is always injective.
            let key_to_index = index_to_key.invert();
            index_to_key.lemma_invert_is_injective();
            assert(key_to_index.is_injective());

            // Next, prove inverting key_to_index results in the original index_to_key map.
            // This helps establish that the values of one of the maps is the domain of the other
            assert forall|x, y| x != y && index_to_key.dom().contains(x) && index_to_key.dom().contains(y) implies
                #[trigger] index_to_key[x] != #[trigger] index_to_key[y] by {
                assert(trigger_main_entry(x));
                assert(trigger_main_entry(y));
            }
            lemma_injective_map_is_invertible(index_to_key);

            // We also invoke a helper lemma to prove that each key-index pair in key_to_index
            // has a corresponding index-key pair in index_to_keys. This helps prove that 
            // index values in key_to_index are valid indices in the main table.
            lemma_injective_map_inverse(key_to_index);

            assert forall |k| #[trigger] key_to_index.contains_key(k) implies {
                let i = key_to_index[k];
                &&& self@.contains_key(i)
                &&& self@.contents[i].key() == k
            } by {
                let i = key_to_index[k];
                assert(self.main_table@.durable_main_table[i] is Some ==> self@.contains_key(i));
            }
        }

        // Same as the proof above, but specifically for tentative state
        pub proof fn lemma_main_table_index_key_tentative(self) 
            requires
                self.inv(),
                self.tentative_view_inv(),
            ensures 
                ({
                    let tentative_view = self.tentative_view().unwrap();
                    let index_to_key = Map::new(
                        |i: int| tentative_view.contents.dom().contains(i),
                        |i: int| tentative_view.contents[i].key
                    );
                    let key_to_index = index_to_key.invert();
                    &&& forall |k| #[trigger] key_to_index.contains_key(k) ==> {
                            let index = key_to_index[k];
                            &&& tentative_view.contains_key(index)
                            &&& tentative_view.contents[index].key() == k
                        }
                    &&& index_to_key.is_injective()
                })
        {
            let tentative_view = self.tentative_view().unwrap();
            let index_to_key = Map::new(
                |i: int| tentative_view.contents.dom().contains(i),
                |i: int| tentative_view.contents[i].key
            );

            // Prove that there are no duplicate keys in the main table; this implies that index_to_key 
            // in injective, which is crucial for the rest of the proof.
            assert(no_duplicate_keys(self.main_table.tentative_view().durable_main_table));

            // key_to_index is also injective since the inverse of a map is always injective.
            let key_to_index = index_to_key.invert();
            index_to_key.lemma_invert_is_injective();
            assert(key_to_index.is_injective());

            // Next, prove inverting key_to_index results in the original index_to_key map.
            // This helps establish that the values of one of the maps is the domain of the other
            assert forall|x, y| x != y && index_to_key.dom().contains(x) && index_to_key.dom().contains(y) implies
                #[trigger] index_to_key[x] != #[trigger] index_to_key[y] by {
                assert(trigger_main_entry(x));
                assert(trigger_main_entry(y));
            }
            lemma_injective_map_is_invertible(index_to_key);

            // We also invoke a helper lemma to prove that each key-index pair in key_to_index
            // has a corresponding index-key pair in index_to_keys. This helps prove that 
            // index values in key_to_index are valid indices in the main table.
            lemma_injective_map_inverse(key_to_index);
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
                old(pm_region)@.flush_predicted(),
                overall_metadata.region_size == old(pm_region)@.len(),
                memory_correctly_set_up_on_region::<K, I, L>(old(pm_region)@.durable_state, kvstore_id),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr),
                overall_metadata.kvstore_id == kvstore_id,
                deserialize_version_metadata(old(pm_region)@.durable_state) == version_metadata,
                deserialize_version_crc(old(pm_region)@.durable_state) == version_metadata.spec_crc(),
                deserialize_overall_metadata(old(pm_region)@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata,
                deserialize_overall_crc(old(pm_region)@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata.spec_crc(),
           ensures 
                pm_region.inv(),
                match result {
                    Ok(()) => {
                        &&& pm_region@.flush_predicted()
                        &&& memory_correctly_set_up_on_region::<K, I, L>(pm_region@.durable_state, kvstore_id)
                        &&& Self::physical_recover(pm_region@.durable_state, version_metadata, overall_metadata) matches Some(recovered_view)
                        &&& recovered_view == DurableKvStoreView::<K, I, L>::init()
                        &&& deserialize_version_metadata(pm_region@.durable_state) == version_metadata
                        &&& deserialize_version_crc(pm_region@.durable_state) == version_metadata.spec_crc()
                        &&& deserialize_overall_metadata(pm_region@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata
                        &&& deserialize_overall_crc(pm_region@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata.spec_crc()
                    }
                    Err(_) => true
                }
        {
            proof {
                pm_region.lemma_inv_implies_view_valid();
            }

            let num_keys = overall_metadata.num_keys;
            let overall_metadata_addr = version_metadata.overall_metadata_addr;

            // Define subregions for each durable component and call setup on each one
            let ghost main_table_writable_addr_fn = |addr: int| overall_metadata.main_table_addr <= addr < overall_metadata.main_table_addr + overall_metadata.main_table_size;
            let main_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.main_table_addr, 
                Ghost(overall_metadata.main_table_size as nat),
                Ghost(main_table_writable_addr_fn)
            );
            
            MainTable::<K>::setup::<PM, L>(&main_table_subregion, pm_region, num_keys, overall_metadata.main_table_entry_size)?;
            proof { 
                main_table_subregion.lemma_reveal_opaque_inv(pm_region); 

                let bytes = pm_region@.read_state;
                let main_table_bytes = extract_bytes(bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                assert(main_table_bytes == main_table_subregion.view(pm_region).read_state);
            }

            // Both the item table and list region do not require any writes in setup; we just need to prove that regardless of the contents of 
            // the PM in those areas, if we set up the item table correctly then 
            let ghost writable_addr_fn = |addr: int| true;
            let item_table_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.item_table_addr, 
                Ghost(overall_metadata.item_table_size as nat),
                Ghost(writable_addr_fn)
            );

            proof {
                DurableItemTable::<K, I>::lemma_table_is_empty_at_setup::<PM, L>(&item_table_subregion, pm_region,
                                                                                 Set::empty(), num_keys);
            }
            let list_area_subregion = WritablePersistentMemorySubregion::new(
                pm_region, 
                overall_metadata.list_area_addr, 
                Ghost(overall_metadata.list_area_size as nat),
                Ghost(writable_addr_fn)
            );
            proof {
                assert(list_area_subregion.view(pm_region).durable_state =~=
                       list_area_subregion.view(pm_region).read_state);
                DurableList::<K, L>::lemma_list_is_empty_at_setup(&list_area_subregion, pm_region,
                                                                  AbstractOpLogState::initialize(), num_keys, 
                                                                  overall_metadata.list_node_size,
                                                                  overall_metadata.num_list_entries_per_node,
                                                                  overall_metadata.num_list_nodes,
                                                                  MainTableView::<K>::init(num_keys))
            }

            let ghost pre_log_setup_bytes = pm_region@.read_state;

            UntrustedLogImpl::setup::<PM, K>(pm_region, overall_metadata.log_area_addr, overall_metadata.log_area_size)?;

            pm_region.flush();

            proof {
                // TODO: refactor this into a lemma
                let bytes = pm_region@.durable_state;
                let recovered_view = Self::physical_recover(bytes, version_metadata, overall_metadata);
                // assert(recovered_view is Some);
                lemma_establish_extract_bytes_equivalence(pre_log_setup_bytes, bytes);

                // First, prove that the recovered view is Some if recovery of all of the other components succeeds.
                // For most of these, we just need to prove that the log setup function didn't modify the corresponding bytes,
                // which is already part of log setup's postcondition, but we need to invoke lemma_subrange_of_extract_bytes_equal
                // to make Verus do the required reasoning about subranges.

                let recovered_log = UntrustedOpLog::<K, L>::recover(bytes, version_metadata, overall_metadata).unwrap();
                let recovered_bytes = apply_physical_log_entries(bytes, recovered_log.physical_op_list).unwrap();

                // Main table recovery succeeds
                let main_table_bytes = extract_bytes(recovered_bytes, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let recovered_main_table = parse_main_table::<K>(main_table_bytes, overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                lemma_subrange_of_extract_bytes_equal(recovered_bytes, 0, overall_metadata.main_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.main_table_size as nat);

                assert(forall |i: int| 0 <= i < recovered_main_table.unwrap().durable_main_table.len() ==> 
                    #[trigger] recovered_main_table.unwrap().durable_main_table[i] is None);

                // Item table recover succeeds
                let item_table_bytes = extract_bytes(recovered_bytes, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let valid_indices = recovered_main_table.unwrap().valid_item_indices();
                lemma_subrange_of_extract_bytes_equal(recovered_bytes, 0, overall_metadata.item_table_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.item_table_size as nat);

                // List recover succeeds
                let list_area_bytes = extract_bytes(recovered_bytes, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                lemma_subrange_of_extract_bytes_equal(recovered_bytes, 0, overall_metadata.list_area_addr as nat, overall_metadata.log_area_addr as nat, overall_metadata.list_area_size as nat);

                DurableList::<K, L>::lemma_parse_each_list_succeeds_if_no_valid_metadata_entries(
                    recovered_main_table.unwrap().durable_main_table,
                    list_area_bytes,
                    Map::empty(),
                    overall_metadata.list_node_size,
                    overall_metadata.num_list_entries_per_node,
                );

                // Now need to prove that the recovered view matches init, i.e. that it results in an empty map.
                assert(recovered_view.unwrap().contents =~= Map::<int, DurableKvStoreViewEntry<K, I, L>>::empty());

//                lemma_if_no_outstanding_writes_to_region_then_flush_is_idempotent(old(pm_region)@);
                lemma_establish_extract_bytes_equivalence(bytes, old(pm_region)@.read_state);
                assert(memory_correctly_set_up_on_region::<K, I, L>(bytes, kvstore_id));
            }

            Ok(())
        }

        pub proof fn lemma_log_size_does_not_overflow_u64(
            pm: PersistentMemoryRegionView,
            version_metadata: VersionMetadata, 
            overall_metadata: OverallMetadata, 
        )
            requires 
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= pm.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                pm.len() == overall_metadata.region_size,
                DurableKvStore::<Perm, PM, K, I, L>::physical_recover(pm.durable_state, version_metadata, overall_metadata) is Some,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& base_log_state.log.len() > u64::spec_size_of()
                }),
            ensures 
                ({
                    let base_log_state = UntrustedLogImpl::recover(pm.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    &&& abstract_op_log matches Some(abstract_log)
                    &&& 0 <= abstract_log.len() <= u64::MAX
                })
        {
            let base_log_state = UntrustedLogImpl::recover(pm.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
            let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
            UntrustedOpLog::<K, L>::lemma_num_log_entries_less_than_or_equal_to_log_bytes_len(0, phys_op_log_buffer.len(), 
                phys_op_log_buffer, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat, 
                overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
        }

        pub exec fn start(
            mut powerpm_region: PoWERPersistentMemoryRegion<Perm, PM>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            Tracked(perm): Tracked<&Perm>,
            Ghost(state): Ghost<DurableKvStoreView<K, I, L>>,
        ) -> (result: Result<(Self, Vec<(Box<K>, u64, u64)>), KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires
                powerpm_region.inv(),
                powerpm_region@.flush_predicted(),
                version_metadata == deserialize_version_metadata(powerpm_region@.durable_state),
                overall_metadata == deserialize_overall_metadata(powerpm_region@.durable_state,
                                                                 version_metadata.overall_metadata_addr),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= powerpm_region@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                forall |s| {
                    &&& #[trigger] Self::physical_recover(s, version_metadata, overall_metadata) == Some(state) 
                    &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
                } ==> perm.check_permission(s),
                powerpm_region@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    ||| base_log_state.log.len() == 0 
                    ||| {
                            &&& abstract_op_log matches Some(abstract_log)
                            &&& 0 <= abstract_log.len() <= u64::MAX
                        } 
                }),
                K::spec_size_of() > 0,
                memory_correctly_set_up_on_region::<K, I, L>(powerpm_region@.durable_state, overall_metadata.kvstore_id),
                // TODO: move these into one of the metadata validity spec fns
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                overall_metadata.item_size + u64::spec_size_of() <= u64::MAX,
                vstd::std_specs::hash::obeys_key_model::<K>(),
                perm.check_permission(powerpm_region@.durable_state),
            ensures
                perm.check_permission(powerpm_region@.durable_state),
                match result {
                    // the primary postcondition is just that we've recovered to the target state, which 
                    // is required by the precondition to be the physical recovery view of the powerpm_region we passed in.
                    Ok((kvstore, entry_list)) => {
                        let entry_list_view = Seq::new(entry_list@.len(), |i: int| (*entry_list[i].0, entry_list[i].1, entry_list[i].2));

                        &&& kvstore@ == state
                        &&& Some(kvstore@) == kvstore.tentative_view()
                        &&& kvstore.valid()
                        &&& kvstore.powerpm_view().flush_predicted()
                        &&& kvstore.constants() == powerpm_region.constants()

                        &&& memory_correctly_set_up_on_region::<K, I, L>(kvstore.powerpm_view().durable_state, overall_metadata.kvstore_id)
                        &&& deserialize_version_metadata(kvstore.powerpm_view().durable_state) == version_metadata
                        &&& deserialize_overall_metadata(kvstore.powerpm_view().durable_state, version_metadata.overall_metadata_addr) == overall_metadata
                        &&& Self::physical_recover(kvstore.powerpm_view().durable_state, version_metadata, overall_metadata) == Some(state)

                        &&& entry_list_view.to_set() == kvstore.key_index_list_view()

                        &&& !kvstore.transaction_committed()

                        // no duplicate keys
                        &&& forall |k: int, l: int| {
                                &&& 0 <= k < entry_list.len()
                                &&& 0 <= l < entry_list.len()
                                &&& k != l
                            } ==> *(#[trigger] entry_list@[k]).0 != *(#[trigger] entry_list@[l]).0
                        // all keys in the key index list correspond to an entry in the kvstore
                        &&& forall |val| kvstore.key_index_list_view().contains(val) ==> {
                            &&& kvstore@[val.1 as int] matches Some(entry)
                            &&& val.0 == entry.key()
                        }
                        // all entries in the kvstore correspond to an element of the key index list
                        &&& forall |i: int| #[trigger] kvstore@.contains_key(i) ==> {
                            exists |v| {
                                &&& #[trigger] kvstore.key_index_list_view().contains(v)
                                &&& v.1 == i
                            }
                        }
                    }
                    Err(KvError::CRCMismatch) => !powerpm_region.constants().impervious_to_corruption(),
                    Err(_) => false 
                }
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);

            let ghost old_powerpm = powerpm_region;
            // 1. Start the log and obtain logged operations (if any)
            // We obtain physical log entries in an unparsed vector as parsing them would require an additional copy in DRAM
            let (mut op_log, phys_log) = UntrustedOpLog::<K, L>::start(&powerpm_region, version_metadata, overall_metadata)?;
            assert(op_log.inv(powerpm_region@, version_metadata, overall_metadata));

            // 2. Replay the log onto the entire PM region
            // Log entries are replayed blindly onto bytes; components do not have their own
            // replay functions. We only parse them after finishing log replay

            if phys_log.len() > 0 {
                Self::install_and_clear_log(
                    &mut powerpm_region,
                    overall_metadata,
                    version_metadata,
                    &mut op_log,
                    phys_log,
                    Tracked(perm),
                    Ghost(state),
                )?;

                proof {
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let true_final_state = apply_physical_log_entries(old_powerpm@.durable_state, phys_log_view).unwrap();
                    lemma_log_replay_preserves_size(old_powerpm@.durable_state, phys_log_view);
                    assert(states_differ_only_in_log_region(true_final_state, powerpm_region@.durable_state, 
                        overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                        true_final_state, powerpm_region@.durable_state, version_metadata, overall_metadata);
                    assert(Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state));
                }
            } 

            proof {
                // The log is now empty, either because it was to begin with or because we cleared it
                op_log.lemma_reveal_opaque_op_log_inv(powerpm_region, version_metadata, overall_metadata);
//                assert(powerpm_region@.can_crash_as(powerpm_region@.read_state));
                assert(UntrustedOpLog::<K, L>::recover(powerpm_region@.read_state, version_metadata, overall_metadata) == Some(AbstractOpLogState::initialize()));
                assert(op_log@ == AbstractOpLogState::initialize());
            }
            
            // We can now start the rest of the components. 
            // We've already played the log, so we won't do any additional writes from this point on.
            // We use read-only subregions to make reasoning about each region separately easier

            let pm_region = powerpm_region.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.main_table_addr, Ghost(overall_metadata.main_table_size as nat));
            let item_table_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.item_table_addr, Ghost(overall_metadata.item_table_size as nat));
            let list_area_subregion = PersistentMemorySubregion::new(pm_region, overall_metadata.list_area_addr, Ghost(overall_metadata.list_area_size as nat));
            proof {
                // Prove that since we know overall recovery succeeded, parsing/starting the rest of the components will also succeed
                let mem = pm_region@.durable_state;
                let main_table_region = extract_bytes(mem, overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let item_table_region = extract_bytes(mem, overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);
                let list_area_region = extract_bytes(mem, overall_metadata.list_area_addr as nat, overall_metadata.list_area_size as nat);
                assert(main_table_region == main_table_subregion.view(pm_region).durable_state);
                assert(item_table_region == item_table_subregion.view(pm_region).durable_state);
                assert(list_area_region == list_area_subregion.view(pm_region).durable_state);

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
                powerpm: powerpm_region,
                pending_updates: Vec::new(),
            };

            proof {
                let recovered_log = UntrustedOpLog::<K, L>::recover(old_powerpm@.durable_state, version_metadata, overall_metadata).unwrap();
                let physical_log_entries = recovered_log.physical_op_list;
                assert(states_differ_only_in_log_region(
                    apply_physical_log_entries(old_powerpm@.durable_state, physical_log_entries).unwrap(),
                    powerpm_region@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                );

                // each recovered component parses correctly
                assert(parse_main_table::<K>(main_table_subregion.view(pm_region).durable_state, overall_metadata.num_keys, overall_metadata.main_table_entry_size).unwrap() == main_table@);
                assert(parse_item_table::<I, K>(item_table_subregion.view(pm_region).durable_state, overall_metadata.num_keys as nat, main_table@.valid_item_indices()).unwrap() == item_table@);
                   /* REMOVED UNTIL WE IMPLEMENT LISTS
                assert(DurableList::<K, L>::parse_all_lists(main_table@, list_area_subregion.view(pm_region).durable_state, overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node).unwrap() == durable_list@);
                   */

                assert(durable_kv_store@ == Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata).unwrap());
                assert(durable_kv_store@ == Self::recover_from_component_views(main_table@, item_table@));
                assert(PhysicalOpLogEntry::vec_view(durable_kv_store.pending_updates) == durable_kv_store.log@.physical_op_list);

//                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(
//                    durable_kv_store.powerpm@);
                durable_kv_store.lemma_if_every_component_recovers_to_its_current_state_then_self_does();

                // the key index list contains an element corresponding to each entry in the durable store
                assert forall |i: u64| #[trigger] durable_kv_store@.contains_key(i as int) implies {
                    exists |v| {
                        &&& #[trigger] durable_kv_store.key_index_list_view().contains(v)
                        &&& v.1 == i
                    }
                } by {
                    let entry = durable_kv_store.main_table@.durable_main_table[i as int].unwrap();
                    let witness = (entry.key(), i, entry.item_index());
                    assert(durable_kv_store.key_index_list_view().contains(witness));
                }

                assert(memory_correctly_set_up_on_region::<K, I, L>(durable_kv_store.powerpm@.durable_state, overall_metadata.kvstore_id)) by {
                    broadcast use pmcopy_axioms;
                    lemma_establish_extract_bytes_equivalence(durable_kv_store.powerpm@.durable_state, old_powerpm@.durable_state);
                    assert(deserialize_version_metadata(durable_kv_store.powerpm@.durable_state) == version_metadata);
                    assert(deserialize_overall_metadata(durable_kv_store.powerpm@.durable_state, version_metadata.overall_metadata_addr) == overall_metadata);
                    assert(deserialize_version_crc(old_powerpm@.durable_state) == deserialize_version_crc(durable_kv_store.powerpm@.durable_state));
                    assert(deserialize_overall_crc(old_powerpm@.durable_state, version_metadata.overall_metadata_addr) == deserialize_overall_crc(durable_kv_store.powerpm@.durable_state, version_metadata.overall_metadata_addr));
                }

                // these last few assignments/assertions hit some necessary triggers
                let tentative_state_bytes = apply_physical_log_entries(powerpm_region@.read_state, op_log@.physical_op_list);
                let tentative_main_table_bytes = extract_bytes(tentative_state_bytes.unwrap(), 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                assert(tentative_main_table_bytes == main_table_subregion.view(pm_region).durable_state);

                let tentative_item_table_bytes = extract_bytes(tentative_state_bytes.unwrap(), 
                    overall_metadata.item_table_addr as nat, overall_metadata.item_table_size as nat);

                reveal(MainTable::opaquable_inv);
                reveal(DurableItemTable::opaquable_inv);

                assert(tentative_item_table_bytes == item_table_subregion.view(pm_region).durable_state);
                assert(durable_kv_store.tentative_item_table() == durable_kv_store.item_table.tentative_view());

                durable_kv_store.lemma_tentative_view_matches_durable_when_log_is_empty();
            }

            Ok((durable_kv_store, entry_list))
        }

        exec fn install_and_clear_log(
            powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PM>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
            op_log: &mut UntrustedOpLog<K, L>,
            phys_log: Vec<PhysicalOpLogEntry>,
            Tracked(perm): Tracked<&Perm>,
            Ghost(state): Ghost<DurableKvStoreView<K, I, L>>,
        ) -> (result: Result<(), KvError<K>>) 
            where 
                PM: PersistentMemoryRegion,
            requires 
                old(powerpm_region).inv(),
                old(powerpm_region)@.flush_predicted(),
                version_metadata == deserialize_version_metadata(old(powerpm_region)@.durable_state),
                overall_metadata == deserialize_overall_metadata(old(powerpm_region)@.durable_state,
                                                                version_metadata.overall_metadata_addr),
                Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata, overall_metadata) == Some(state),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr),
                overall_metadata.log_area_addr + overall_metadata.log_area_size <= old(powerpm_region)@.len() <= u64::MAX,
                overall_metadata.log_area_size >= spec_log_area_pos() + MIN_LOG_AREA_SIZE,
                forall |s| {
                    &&& #[trigger] Self::physical_recover(s, version_metadata, overall_metadata) == Some(state) 
                    &&& version_and_overall_metadata_match_deserialized(s, old(powerpm_region)@.durable_state)
                } ==> perm.check_permission(s),
                old(powerpm_region)@.len() == overall_metadata.region_size,
                ({
                    let base_log_state = UntrustedLogImpl::recover(old(powerpm_region)@.durable_state, overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat).unwrap();
                    let phys_op_log_buffer = extract_bytes(base_log_state.log, 0, (base_log_state.log.len() - u64::spec_size_of()) as nat);
                    let abstract_op_log = UntrustedOpLog::<K, L>::parse_log_ops(phys_op_log_buffer, overall_metadata.log_area_addr as nat, 
                            overall_metadata.log_area_size as nat, overall_metadata.region_size as nat, version_metadata.overall_metadata_addr as nat);
                    ||| base_log_state.log.len() == 0 
                    ||| {
                            &&& abstract_op_log matches Some(abstract_log)
                            &&& 0 <= abstract_log.len() <= u64::MAX
                        } 
                }),
                K::spec_size_of() > 0,
                memory_correctly_set_up_on_region::<K, I, L>(old(powerpm_region)@.durable_state, overall_metadata.kvstore_id),
                // TODO: move these into one of the metadata validity spec fns
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                0 <= overall_metadata.log_area_addr < overall_metadata.log_area_addr + overall_metadata.log_area_size <= overall_metadata.region_size,
                overall_metadata.item_size + u64::spec_size_of() <= u64::MAX,
                vstd::std_specs::hash::obeys_key_model::<K>(),

                0 < version_metadata.overall_metadata_addr < 
                    version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() + u64::spec_size_of() <=
                    overall_metadata.log_area_addr,
                old(op_log).inv(old(powerpm_region)@, version_metadata, overall_metadata),
                ({
                    let log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    AbstractPhysicalOpLogEntry::log_inv(log_view, version_metadata, overall_metadata)
                }),
                phys_log@.len() > 0,
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(old(powerpm_region)@.durable_state, version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                old(op_log).base_log_view() == old(op_log).base_log_view().drop_pending_appends(),
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(old(powerpm_region)@.durable_state, version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log == old(op_log)@
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                    &&& abstract_op_log.op_list_committed
                    &&& abstract_op_log.physical_op_list.len() > 0
                }),
                perm.check_permission(old(powerpm_region)@.durable_state),
            ensures
                perm.check_permission(old(powerpm_region)@.durable_state),
                match result {
                    Ok(()) => {
                        &&& powerpm_region.inv()
                        &&& powerpm_region@.flush_predicted()
                        &&& powerpm_region.constants() == old(powerpm_region).constants()
                        &&& version_metadata == deserialize_version_metadata(powerpm_region@.durable_state)
                        &&& overall_metadata == deserialize_overall_metadata(powerpm_region@.durable_state,
                                                                        version_metadata.overall_metadata_addr)
                        &&& Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state)
                        &&& op_log.inv(powerpm_region@, version_metadata, overall_metadata)
                        &&& !op_log@.op_list_committed
                        &&& op_log@.physical_op_list.len() == 0
                        // install log postconditions
                        &&& ({
                                let true_recovery_state = Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata, overall_metadata).unwrap();
                                let recovery_state = Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata);
                                &&& recovery_state matches Some(recovery_state)
                                &&& recovery_state == true_recovery_state
                            })
                        &&& ({
                                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                                let true_final_state = apply_physical_log_entries(old(powerpm_region)@.durable_state, phys_log_view);
                                states_differ_only_in_log_region(true_final_state.unwrap(), powerpm_region@.durable_state, 
                                    overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat)
                            })
                        &&& version_and_overall_metadata_match_deserialized(old(powerpm_region)@.durable_state, powerpm_region@.durable_state)
                    }
                    Err(_) => false 
                }
        {
            let ghost old_powerpm = *powerpm_region;

            proof { PhysicalOpLogEntry::lemma_abstract_log_inv_implies_concrete_log_inv(phys_log, version_metadata, overall_metadata); }

            Self::install_log(powerpm_region, version_metadata, overall_metadata, &phys_log, Tracked(perm));

            proof { 
                op_log.lemma_same_bytes_preserve_op_log_invariant(old_powerpm, *powerpm_region, version_metadata, overall_metadata);
                assert(apply_physical_log_entries(old_powerpm@.durable_state, op_log@.physical_op_list).unwrap() == powerpm_region@.durable_state);
                assert(Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state));
                assert({
                    &&& version_metadata == deserialize_version_metadata(powerpm_region@.durable_state)
                    &&& overall_metadata == deserialize_overall_metadata(powerpm_region@.durable_state,
                                                                    version_metadata.overall_metadata_addr)
                });
            }
            let ghost recovered_log = UntrustedOpLog::<K, L>::recover(old_powerpm@.durable_state, version_metadata, overall_metadata).unwrap();
            let ghost physical_log_entries = recovered_log.physical_op_list;

            // We can now clear the log, since we have installed and flushed it.
            let ghost crash_pred = |s: Seq<u8>| {
                &&& Self::physical_recover(s, version_metadata, overall_metadata) == Some(state) 
                &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
            };
            proof {
                assert(Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state));
//                assert(powerpm_region@.can_crash_as(powerpm_region@.durable_state));
                assert(powerpm_region@.flush_predicted());
//                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(powerpm_region@);
//                assert(forall |s| powerpm_region@.can_crash_as(s) ==> s == powerpm_region@.durable_state);
                Self::lemma_clear_log_is_crash_safe(*powerpm_region, *op_log, version_metadata,
                    overall_metadata, crash_pred, state, perm,);
            }

            let ghost pre_clear_powerpm = *powerpm_region;
            op_log.clear_log(powerpm_region, version_metadata, overall_metadata, Ghost(crash_pred), Tracked(perm))?;

            proof {
                assert(states_differ_only_in_log_region(pre_clear_powerpm@.durable_state, powerpm_region@.durable_state, 
                    overall_metadata.log_area_addr as nat, overall_metadata.log_area_size as nat));
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    pre_clear_powerpm@.durable_state, powerpm_region@.durable_state, version_metadata, overall_metadata);
                assert(Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == Some(state));
                Self::lemma_metadata_unchanged_when_views_differ_only_in_log_region(pre_clear_powerpm@, powerpm_region@, 
                    version_metadata, overall_metadata);
                assert(version_and_overall_metadata_match_deserialized(old(powerpm_region)@.durable_state, powerpm_region@.durable_state));
            }

            Ok(())
        }


        // This function installs the log by blindly replaying physical log entries onto the WRPM region. All writes
        // made by this function are crash-safe; if we crash during this operation, replaying the full log on the resulting
        // crash state gets us to the final desired state. This function does not return a Result because it cannot fail
        // as long as the log is well-formed, which is required by the precondition.
        fn install_log(
            powerpm_region: &mut PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            phys_log: &Vec<PhysicalOpLogEntry>,
            Tracked(perm): Tracked<&Perm>,
        ) 
            where 
                PM: PersistentMemoryRegion,
                Perm: CheckPermission<Seq<u8>>,
            requires
                old(powerpm_region).inv(),
                old(powerpm_region)@.flush_predicted(),
                old(powerpm_region)@.len() == overall_metadata.region_size,
                PhysicalOpLogEntry::log_inv(*phys_log, version_metadata, overall_metadata),
                phys_log.len() > 0,
                UntrustedLogImpl::recover(old(powerpm_region)@.durable_state, overall_metadata.log_area_addr as nat,
                                          overall_metadata.log_area_size as nat) is Some,
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(old(powerpm_region)@.read_state,
                                                                          version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                forall |s| {
                    &&& Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata,
                                             overall_metadata) ==
                       Self::physical_recover(s, version_metadata, overall_metadata) 
                    &&& version_and_overall_metadata_match_deserialized(s, old(powerpm_region)@.durable_state)
                } ==> #[trigger] perm.check_permission(s),
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                0 <= overall_metadata.log_area_addr <
                    overall_metadata.log_area_addr + overall_metadata.log_area_size <=
                    overall_metadata.region_size,
                0 < spec_log_header_area_size() <= spec_log_area_pos() < overall_metadata.log_area_size,
                Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata,
                                       overall_metadata) is Some,
                deserialize_version_metadata(old(powerpm_region)@.durable_state) == version_metadata,
                overall_metadata == deserialize_overall_metadata(old(powerpm_region)@.durable_state,
                                                                 version_metadata.overall_metadata_addr),
            ensures
                powerpm_region.inv(),
                powerpm_region@.flush_predicted(),
                powerpm_region@.len() == overall_metadata.region_size,
                powerpm_region.constants() == old(powerpm_region).constants(),
                perm.check_permission(powerpm_region@.durable_state),
                ({
                    let true_recovery_state = Self::physical_recover(old(powerpm_region)@.durable_state,
                                                                     version_metadata,
                                                                     overall_metadata).unwrap();
                    let recovery_state = Self::physical_recover(powerpm_region@.durable_state, version_metadata,
                                                                overall_metadata);
                    &&& recovery_state matches Some(recovery_state)
                    &&& recovery_state == true_recovery_state
                }),
                ({
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    let true_final_state = apply_physical_log_entries(old(powerpm_region)@.read_state,
                                                                      phys_log_view);
                    true_final_state == Some(powerpm_region@.read_state)
                }),
                ({
                    let abstract_op_log = UntrustedOpLog::<K, L>::recover(powerpm_region@.read_state,
                                                                          version_metadata, overall_metadata);
                    let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                    &&& abstract_op_log matches Some(abstract_op_log)
                    &&& abstract_op_log.physical_op_list == phys_log_view
                    &&& AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata)
                }),
                extract_bytes(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(old(powerpm_region)@.durable_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                extract_bytes(powerpm_region@.read_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(old(powerpm_region)@.read_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                version_and_overall_metadata_match_deserialized(old(powerpm_region)@.durable_state,
                                                                powerpm_region@.durable_state),  
                version_and_overall_metadata_match_deserialized(old(powerpm_region)@.read_state,
                                                                powerpm_region@.read_state),  
        {
            let log_start_addr = overall_metadata.log_area_addr;
            let log_size = overall_metadata.log_area_size;
            let region_size = overall_metadata.region_size;

            let ghost old_phys_log = phys_log;
            let ghost old_powerpm = powerpm_region@;
            let ghost old_powerpm_constants = powerpm_region.constants();

            let ghost final_recovery_state = Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata, overall_metadata).unwrap();

            let mut index = 0;

            proof {
                let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                let replayed_ops = phys_log_view.subrange(0, index as int);
                let remaining_ops = phys_log_view.subrange(index as int, phys_log.len() as int);
                let final_mem = apply_physical_log_entries(old_powerpm.durable_state, phys_log_view).unwrap();
                let current_mem = apply_physical_log_entries(old_powerpm.durable_state, replayed_ops).unwrap();

                assert(replayed_ops.len() == 0);
                assert(remaining_ops == phys_log_view);
                assert(current_mem == old_powerpm.durable_state);
                assert(apply_physical_log_entries(old_powerpm.durable_state, remaining_ops).unwrap() == final_mem);
                powerpm_region.lemma_inv_implies_view_valid();
            }

            while index < phys_log.len() 
                invariant
                    old_powerpm.valid(),
                    old_powerpm.flush_predicted(),
                    old_powerpm == old(powerpm_region)@,
                    old_powerpm.len() == powerpm_region@.len(),
                    ({
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        let log = UntrustedOpLog::<K, L>::recover(old_powerpm.durable_state, version_metadata,
                                                                  overall_metadata);
                        &&& log matches Some(log)
                        &&& log.physical_op_list == phys_log_view      
                    }),
                    Some(final_recovery_state) ==
                        Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata,
                                               overall_metadata),
                    PhysicalOpLogEntry::log_inv(*phys_log, version_metadata, overall_metadata),
                    forall |s| {
                        &&& Self::physical_recover(s, version_metadata, overall_metadata) ==
                           Some(final_recovery_state)
                        &&& version_and_overall_metadata_match_deserialized(s, powerpm_region@.durable_state)
                    } ==> #[trigger] perm.check_permission(s),
                    Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) == 
                        Some(final_recovery_state),
                    old_phys_log == phys_log,
                    ({
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);
                        recovery_write_region_invariant::<Perm, PM, K, I, L>(*powerpm_region, version_metadata,
                                                                             overall_metadata, phys_log_view)
                    }),
                    0 <= index <= phys_log.len(),
                    old_powerpm_constants == powerpm_region.constants(),
                    VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                    version_and_overall_metadata_match_deserialized(old_powerpm.durable_state,
                                                                    powerpm_region@.durable_state),
                    version_and_overall_metadata_match_deserialized(old_powerpm.read_state,
                                                                    powerpm_region@.read_state),
                    deserialize_version_metadata(old_powerpm.durable_state) == version_metadata,
                    overall_metadata == deserialize_overall_metadata(old_powerpm.durable_state,
                                                                     version_metadata.overall_metadata_addr),
                    no_outstanding_writes_in_range(powerpm_region@, overall_metadata.log_area_addr as int,
                                                   overall_metadata.log_area_addr +
                                                   overall_metadata.log_area_size),
                    no_outstanding_writes_to_version_metadata(powerpm_region@),
                    no_outstanding_writes_to_overall_metadata(powerpm_region@,
                                                              version_metadata.overall_metadata_addr as int),
                    states_have_matching_metadata(old_powerpm.durable_state, powerpm_region@.durable_state,
                                                  version_metadata, overall_metadata),
                    extract_bytes(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat) ==
                        extract_bytes(old_powerpm.durable_state, overall_metadata.log_area_addr as nat,
                                      overall_metadata.log_area_size as nat),
                    extract_bytes(powerpm_region@.read_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat) ==
                        extract_bytes(old_powerpm.read_state, overall_metadata.log_area_addr as nat,
                                      overall_metadata.log_area_size as nat),
                    ({
                        let phys_log_view = Seq::new(phys_log@.len(), |i: int| phys_log[i]@);

                        let replayed_ops = phys_log_view.subrange(0, index as int);

                        apply_physical_log_entries(old_powerpm.read_state, replayed_ops) ==
                            Some(powerpm_region@.read_state)
                    }),
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
                    lemma_safe_recovery_writes::<Perm, PM, K, I, L>(*powerpm_region, version_metadata,
                                                                    overall_metadata, phys_log_view,
                                                                    op.absolute_addr as int, op.bytes@);

                    assert(extract_bytes(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat) =~=
                           extract_bytes(old_powerpm.durable_state, overall_metadata.log_area_addr as nat,
                                         overall_metadata.log_area_size as nat));
                
                    // Prove that installing this log entry has the intended effect
                    Self::lemma_install_single_log_entry(phys_log_view, index as int, old_powerpm,
                                                         *powerpm_region, 
version_metadata, overall_metadata,
                                                         final_recovery_state);
                }

                let ghost pre_write_powerpm = powerpm_region@;

                assert forall |s| #[trigger] can_result_from_partial_write(s, powerpm_region@.durable_state,
                                                                      op.absolute_addr as int, op.bytes@) implies
                       perm.check_permission(s) by {
                   assert(Self::physical_recover(s, version_metadata, overall_metadata) ==
                          Some(final_recovery_state)
);
                   assert(version_and_overall_metadata_match_deserialized(s, old_powerpm.durable_state)
);
                   assert(Self::physical_recover(old(powerpm_region)@.durable_state, version_metadata,
                                                 overall_metadata) ==
                          Self::physical_recover(s, version_metadata, overall_metadata));
                   assert(version_and_overall_metadata_match_deserialized(s, old(powerpm_region)@.durable_state)
);
                }

                // write the current op's updates to the specified location on storage
                powerpm_region.write(op.absolute_addr, op.bytes.as_slice(), Tracked(perm));

                proof {
                    lemma_auto_can_result_from_partial_write_effect();
                }
             
                assert(extract_bytes(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat,
                                     overall_metadata.log_area_size as nat) =~=
                       extract_bytes(old_powerpm.durable_state, overall_metadata.log_area_addr as nat,
                                     overall_metadata.log_area_size as nat));
                assert(extract_bytes(powerpm_region@.read_state, overall_metadata.log_area_addr as nat,
                                     overall_metadata.log_area_size as nat) =~=
                       extract_bytes(old_powerpm.read_state, overall_metadata.log_area_addr as nat,
                                     overall_metadata.log_area_size as nat));

                proof {
                    lemma_states_have_matching_metadata_implies_metadata_unchanged(
                        old_powerpm.durable_state, powerpm_region@.durable_state,
                        version_metadata, overall_metadata);
                    lemma_states_have_matching_metadata_implies_metadata_unchanged(
                        old_powerpm.read_state, powerpm_region@.read_state,
                        version_metadata, overall_metadata);
                    UntrustedOpLog::<K, L>::lemma_same_bytes_recover_to_same_state(
                        old_powerpm.durable_state,
                        powerpm_region@.durable_state,
                        version_metadata,
                        overall_metadata
                    );
                }

                index += 1;
            }

            powerpm_region.flush();
        }

        // This lemma proves that installing a single log entry preserves various properties about 
        // the entire system
        proof fn lemma_install_single_log_entry(
            phys_log_view: Seq<AbstractPhysicalOpLogEntry>,
            index: int,
            old_powerpm: PersistentMemoryRegionView,
            powerpm_region: PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            final_recovery_state: DurableKvStoreView<K, I, L>,
        )
            requires 
                old_powerpm.valid(),
                old_powerpm.len() == powerpm_region@.len(),
                old_powerpm.flush_predicted(),
                Self::physical_recover(powerpm_region@.durable_state, version_metadata, overall_metadata) ==
                    Some(final_recovery_state),
                recovery_write_region_invariant::<Perm, PM, K, I, L>(powerpm_region, version_metadata,
                                                                     overall_metadata, phys_log_view)
,
                no_outstanding_writes_in_range(powerpm_region@, overall_metadata.log_area_addr as int,
                                               overall_metadata.log_area_addr + overall_metadata.log_area_size),
                0 <= index < phys_log_view.len(),
                extract_bytes(powerpm_region@.durable_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(old_powerpm.durable_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                extract_bytes(powerpm_region@.read_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(old_powerpm.read_state, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                no_outstanding_writes_to_version_metadata(powerpm_region@),
                no_outstanding_writes_to_overall_metadata(powerpm_region@,
                                                          version_metadata.overall_metadata_addr as int),
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                states_have_matching_metadata(old_powerpm.durable_state, powerpm_region@.durable_state,
                                              version_metadata, overall_metadata),
                states_have_matching_metadata(old_powerpm.read_state, powerpm_region@.read_state,
                                              version_metadata, overall_metadata),
                deserialize_version_metadata(old_powerpm.durable_state) == version_metadata,
                deserialize_overall_metadata(old_powerpm.durable_state, version_metadata.overall_metadata_addr) ==
                    overall_metadata,
                AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata),
                ({
                    let replayed_ops = phys_log_view.subrange(0, index as int);

                    apply_physical_log_entries(old_powerpm.read_state, replayed_ops) ==
                        Some(powerpm_region@.read_state)
                }),
            ensures 
                ({
                    let op = phys_log_view[index];
                    let written_powerpm = update_bytes(powerpm_region@.read_state, op.absolute_addr as int, op.bytes);
                    let new_replayed_ops = phys_log_view.subrange(0, index + 1);
                    let replayed_ops = phys_log_view.subrange(0, index as int);
                    let new_mem = apply_physical_log_entries(old_powerpm.read_state, new_replayed_ops);
                    &&& forall |s| #[trigger] can_result_from_partial_write(s, powerpm_region@.durable_state,
                                                                     op.absolute_addr as int, op.bytes) ==> {
                           &&& Self::physical_recover(s, version_metadata, overall_metadata) ==
                                  Some(final_recovery_state)
                           &&& version_and_overall_metadata_match_deserialized(s, old_powerpm.durable_state)
                           &&& states_have_matching_metadata(s, old_powerpm.durable_state,
                                                           version_metadata, overall_metadata)
                    }
                    &&& new_mem == Some(written_powerpm)
                    &&& states_have_matching_metadata(written_powerpm, old_powerpm.read_state,
                                                    version_metadata, overall_metadata)
                    &&& version_and_overall_metadata_match_deserialized(old_powerpm.read_state, written_powerpm)
                }),
        {
            let op = phys_log_view[index];

            lemma_states_have_matching_metadata_implies_metadata_unchanged(
                old_powerpm.durable_state, old_powerpm.read_state, version_metadata, overall_metadata
            );

            assert(op.inv(version_metadata, overall_metadata)); 
            assert({
                ||| op.absolute_addr + op.len <= overall_metadata.log_area_addr
                ||| overall_metadata.log_area_addr + overall_metadata.log_area_size <= op.absolute_addr
            });
            assert(forall |i: int| op.absolute_addr <= i < op.absolute_addr + op.len ==> 
                #[trigger] addr_modified_by_recovery(phys_log_view, i));
            
            lemma_safe_recovery_writes::<Perm, PM, K, I, L>(powerpm_region, version_metadata, 
                overall_metadata, phys_log_view, op.absolute_addr as int, op.bytes);

            let new_replayed_ops = phys_log_view.subrange(0, index + 1);
            let replayed_ops = phys_log_view.subrange(0, index as int);

            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(old_powerpm.durable_state,
                                                                             version_metadata,
                                                                             overall_metadata, new_replayed_ops);

            assert(replayed_ops == new_replayed_ops.subrange(0, new_replayed_ops.len() - 1));

            Self::lemma_installing_single_log_entry_preserves_crash_perm_and_metadata(
                phys_log_view, index, old_powerpm.durable_state, powerpm_region, version_metadata,
                overall_metadata, final_recovery_state
            );

            let new_mem = apply_physical_log_entries(old_powerpm.read_state, new_replayed_ops);
            let written_powerpm = update_bytes(powerpm_region@.read_state, op.absolute_addr as int, op.bytes);
            lemma_establish_extract_bytes_equivalence(new_mem.unwrap(), written_powerpm);
            assert(written_powerpm =~= new_mem.unwrap());

            lemma_states_have_matching_metadata_implies_metadata_unchanged(
                old_powerpm.read_state, written_powerpm, version_metadata, overall_metadata
            );
        }

        proof fn lemma_installing_single_log_entry_preserves_crash_perm_and_metadata(
            phys_log_view: Seq<AbstractPhysicalOpLogEntry>,
            index: int,
            old_powerpm: Seq<u8>,
            current_powerpm: PoWERPersistentMemoryRegion<Perm, PM>,
            version_metadata: VersionMetadata,
            overall_metadata: OverallMetadata,
            final_recovery_state: DurableKvStoreView<K, I, L>,
        )
            requires 
                old_powerpm.len() == current_powerpm@.len(),
                0 <= index < phys_log_view.len(),
                Self::physical_recover(current_powerpm@.durable_state, version_metadata, overall_metadata) == 
                    Some(final_recovery_state),
                extract_bytes(current_powerpm@.durable_state, overall_metadata.log_area_addr as nat,
                              overall_metadata.log_area_size as nat) == 
                    extract_bytes(old_powerpm, overall_metadata.log_area_addr as nat,
                                  overall_metadata.log_area_size as nat),
                AbstractPhysicalOpLogEntry::log_inv(phys_log_view, version_metadata, overall_metadata),
                no_outstanding_writes_to_version_metadata(current_powerpm@),
                no_outstanding_writes_to_overall_metadata(current_powerpm@,
                                                          version_metadata.overall_metadata_addr as int),
                states_have_matching_metadata(old_powerpm, current_powerpm@.durable_state, version_metadata,
                                              overall_metadata),
                deserialize_version_metadata(old_powerpm) == version_metadata,
                deserialize_overall_metadata(old_powerpm, version_metadata.overall_metadata_addr) ==
                    overall_metadata,
                VersionMetadata::spec_size_of() <= version_metadata.overall_metadata_addr,
                recovery_write_region_invariant::<Perm, PM, K, I, L>(current_powerpm, version_metadata,
                                                                     overall_metadata, phys_log_view),
                ({
                    let op = phys_log_view[index];
                    forall |s| can_result_from_partial_write(s, current_powerpm@.durable_state, op.absolute_addr as int,
                                                        op.bytes) ==> {
                        &&& DurableKvStore::<Perm, PM, K, I, L>::physical_recover(
                            s, version_metadata, overall_metadata
                        ) matches Some(crash_recover_state)
                        &&& crash_recover_state == DurableKvStore::<Perm, PM, K, I, L>::physical_recover(
                            current_powerpm@.durable_state, version_metadata, overall_metadata
                        ).unwrap()
                    }
                }),
            ensures 
                ({
                    let op = phys_log_view[index];
                    forall |s| #[trigger] can_result_from_partial_write(s, current_powerpm@.durable_state,
                                                                   op.absolute_addr as int, op.bytes) ==> {
                            &&& Self::physical_recover(s, version_metadata, overall_metadata) ==
                                  Some(final_recovery_state)
                            &&& version_and_overall_metadata_match_deserialized(s, old_powerpm)
                            &&& states_have_matching_metadata(old_powerpm, s, version_metadata, overall_metadata)
                    }
                })
        {
            lemma_states_have_matching_metadata_implies_metadata_unchanged(
                old_powerpm, current_powerpm@.durable_state, version_metadata, overall_metadata
            );
            let op = phys_log_view[index];
            assert forall |s| #[trigger] can_result_from_partial_write(s, current_powerpm@.durable_state,
                                                                  op.absolute_addr as int, op.bytes) implies {
                &&& Self::physical_recover(s, version_metadata, overall_metadata) == Some(final_recovery_state)
                &&& version_and_overall_metadata_match_deserialized(s, old_powerpm)
                &&& states_have_matching_metadata(old_powerpm, s, version_metadata, overall_metadata)
            } by {
                lemma_auto_can_result_from_partial_write_effect();
                lemma_establish_extract_bytes_equivalence(s, current_powerpm@.durable_state);
                lemma_states_have_matching_metadata_implies_metadata_unchanged(old_powerpm, s, version_metadata,
                                                                               overall_metadata);
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
                self.tentative_view().unwrap().contains_key(metadata_index as int),
            ensures
                match result {
                    Ok(item) => {
                        match self.tentative_view().unwrap()[metadata_index as int] {
                            Some(entry) => entry.item() == item,
                            None => false,
                        }
                    },
                    Err(KvError::CRCMismatch) => !self.constants().impervious_to_corruption(),
                    Err(_) => false,
                }
        {
            assert(self.main_table.tentative_view().durable_main_table[metadata_index as int] is Some) by {
                self.lemma_index_in_tentative_view_is_also_in_main_table_tentative_view(metadata_index);
                assert(self.tentative_main_table().durable_main_table[metadata_index as int] is Some);
            }

            let pm = self.powerpm.get_pm_region_ref();
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
                &&& self.main_table.free_list().contains(which_entry as u64)
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
                &&& self.version_metadata == deserialize_version_metadata(s)
                &&& self.overall_metadata == deserialize_overall_metadata(s, self.version_metadata.overall_metadata_addr)
                &&& Some(self.main_table@) ==
                       parse_main_table::<K>(extract_bytes(s, main_table_addr as nat, main_table_size as nat),
                                             num_keys, main_table_entry_size)
                      
                &&& Some(self.item_table@) ==
                       parse_item_table::<I, K>(extract_bytes(s, item_table_addr as nat, item_table_size as nat),
                                                num_keys as nat, self.main_table@.valid_item_indices())
                &&& Some(self@) == Self::physical_recover(s, version_metadata, overall_metadata)
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
            }
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_by_crashing(self)
            requires
                self.inv(),
                !self.log@.op_list_committed,
                self.item_table.durable_valid_indices() == self.main_table@.valid_item_indices(),
            ensures
                self.condition_preserved_by_subregion_masks()(self.powerpm@.durable_state)
        {
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;

            let condition = self.condition_preserved_by_subregion_masks();
            let s = self.powerpm@.durable_state;
            assert(condition(s)) by {
                let recovered_log = UntrustedOpLog::<K, L>::recover(s, self.version_metadata,
                                                                    overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, overall_metadata);
                assert(apply_physical_log_entries(s, recovered_log.unwrap().physical_op_list) == Some(s));
//                lemma_subregion_view_can_crash_as_subrange(self.powerpm@, s, main_table_addr as nat, main_table_size as nat);
//                lemma_subregion_view_can_crash_as_subrange(self.powerpm@, s, item_table_addr as nat, item_table_size as nat);
//                lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(self.powerpm@);
                lemma_establish_extract_bytes_equivalence(s, self.powerpm@.durable_state);
            }
        }

        proof fn lemma_writable_mask_for_main_table_suitable_for_creating_subregion(self, perm: &Perm)
            requires
                self.inv(),
                !self.log@.op_list_committed,
                forall |s| {
                    &&& Self::physical_recover(s, self.spec_version_metadata(), self.spec_overall_metadata()) == Some(self@)
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                self.tentative_main_table() == self.main_table.tentative_view(),
                forall |i: int| self.tentative_view().unwrap().contains_key(i) ==> i < self.overall_metadata.num_keys,
                self.main_table@.valid_item_indices() == self.item_table.durable_valid_indices(),
            ensures
                condition_sufficient_to_create_powerpm_subregion(
                    self.powerpm@, perm, self.overall_metadata.main_table_addr,
                                                                self.overall_metadata.main_table_size as nat,
                    self.get_writable_mask_for_main_table(),
                    self.condition_preserved_by_subregion_masks(),
                )
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
            hide(reverse_item_mapping_exists);

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
                       &&& s1.len() == s2.len() == self.powerpm@.len()
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
                    assert(self.main_table.free_list().contains(which_entry as u64));
                    assert(self.main_table.free_indices().contains(which_entry as u64)) by {
                        reveal(MainTable::opaquable_inv);
                    }
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
                lemma_establish_extract_bytes_equivalence(s1, s2);
                lemma_parse_main_table_doesnt_depend_on_fields_of_invalid_entries::<K>(
                    ss1, ss2, num_keys, main_table_entry_size
                );
                assert(UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata) ==
                       UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, overall_metadata))
                    by {
                    lemma_same_log_bytes_recover_to_same_state(s1, s2, log_area_addr as nat, log_area_size as nat,
                                                               s1.len());
                }
                let recovered_log = UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, overall_metadata);
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, overall_metadata);
                assert(parse_main_table::<K>(extract_bytes(s2, main_table_addr as nat, main_table_size as nat),
                                                 num_keys, main_table_entry_size) ==
                       Some(self.main_table@));
                assert(apply_physical_log_entries(s2, recovered_log.unwrap().physical_op_list) == Some(s2));
                assert(parse_item_table::<I, K>(extract_bytes(s2, item_table_addr as nat, item_table_size as nat),
                                            num_keys as nat, self.main_table@.valid_item_indices()) ==
                      Some(self.item_table@));
                assert(Self::physical_recover(s2, self.version_metadata, overall_metadata) == Some(self@));
            }
        }

        spec fn main_table_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                               self.overall_metadata.main_table_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat)
        }

        spec fn item_table_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                               self.overall_metadata.item_table_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.item_table_addr as nat,
                                   self.overall_metadata.item_table_size as nat)
        }

        spec fn log_area_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.powerpm@, self.overall_metadata.log_area_addr as nat,
                               self.overall_metadata.log_area_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.log_area_addr as nat,
                                   self.overall_metadata.log_area_size as nat)
        }

        spec fn list_area_view_matches(self, pm_view: PersistentMemoryRegionView) -> bool
        {
            get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                               self.overall_metadata.list_area_size as nat) ==
                get_subregion_view(pm_view, self.overall_metadata.list_area_addr as nat,
                                   self.overall_metadata.list_area_size as nat)
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
            self,
            old_self: Self,
            subregion: PoWERPersistentMemorySubregion,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.log@.op_list_committed,
                condition_sufficient_to_create_powerpm_subregion(
                    old_self.powerpm@, perm, old_self.overall_metadata.main_table_addr,
                    old_self.overall_metadata.main_table_size as nat,
                    old_self.get_writable_mask_for_main_table(),
                    old_self.condition_preserved_by_subregion_masks(),
                ),
                subregion.constants() == old_self.powerpm.constants(),
                subregion.start() == old_self.overall_metadata.main_table_addr,
                subregion.len() == old_self.overall_metadata.main_table_size,
                subregion.initial_region_view() == old_self.powerpm@,
                subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_main_table(),
                subregion.inv(&self.powerpm, perm),
                self == (Self{ powerpm: self.powerpm, main_table: self.main_table, ..old_self }),
            ensures
                self.powerpm.inv(),
                self.powerpm.constants() == old_self.powerpm.constants(),
                self.powerpm@.len() == subregion.initial_region_view().len(),
                views_differ_only_where_subregion_allows(subregion.initial_region_view(), self.powerpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat,
                                                         old_self.get_writable_mask_for_main_table()),
                self.item_table_view_matches(old_self.powerpm@),
                self.list_area_view_matches(old_self.powerpm@),
                self.log_area_view_matches(old_self.powerpm@),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    condition(self.powerpm@.durable_state)
                })
        {
            subregion.lemma_reveal_opaque_inv(&self.powerpm);

            assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat));
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat));
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat));
        }

        proof fn lemma_main_table_subregion_grants_access_to_free_slots(
            self,
            subregion: PoWERPersistentMemorySubregion,
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
                &&& self.main_table.free_list().contains(idx)
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
            |addr: int| address_belongs_to_invalid_item_table_entry::<I>(
                addr - self.overall_metadata.item_table_addr,
                self.overall_metadata.num_keys,
                self.item_table.durable_valid_indices().union(self.item_table.tentative_valid_indices())
            )
        }

        proof fn lemma_writable_mask_for_item_table_suitable_for_creating_subregion(
            self,
            perm: &Perm
        )
            requires
                self.inv(),
                !self.log@.op_list_committed,
                forall |s| {
                    &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                } ==> #[trigger] perm.check_permission(s),
                self.tentative_view_inv(),
            ensures
                condition_sufficient_to_create_powerpm_subregion(
                    self.powerpm@, perm, self.overall_metadata.item_table_addr,
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
                       &&& s1.len() == s2.len() == self.powerpm@.len()
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
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, overall_metadata);
                assert(apply_physical_log_entries(s2, recovered_log.unwrap().physical_op_list) == Some(s2));
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
                lemma_establish_extract_bytes_equivalence(s1, s2);
            }
        }

        proof fn lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
            self,
            old_self: Self,
            subregion: PoWERPersistentMemorySubregion,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.log@.op_list_committed,
                old_self.tentative_main_table_valid(),
                old_self.tentative_item_table_valid(),
                old_self.main_table.tentative_view() == old_self.tentative_main_table(),
                old_self.tentative_main_table().valid_item_indices() == old_self.item_table.tentative_valid_indices(),
                condition_sufficient_to_create_powerpm_subregion(
                    old_self.powerpm@, perm, old_self.overall_metadata.item_table_addr,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table(),
                    old_self.condition_preserved_by_subregion_masks(),
                ),
                subregion.constants() == old_self.powerpm.constants(),
                subregion.start() == old_self.overall_metadata.item_table_addr,
                subregion.len() == old_self.overall_metadata.item_table_size,
                subregion.initial_region_view() == old_self.powerpm@,
                subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_item_table(),
                subregion.inv(&self.powerpm, perm),
                self == (Self{ powerpm: self.powerpm, item_table: self.item_table, ..old_self }),
            ensures
                self.powerpm.inv(),
                self.powerpm.constants() == old_self.powerpm.constants(),
                self.powerpm@.len() == subregion.initial_region_view().len(),
                views_differ_only_where_subregion_allows(subregion.initial_region_view(), self.powerpm@,
                                                         self.overall_metadata.item_table_addr as nat,
                                                         self.overall_metadata.item_table_size as nat,
                                                         old_self.get_writable_mask_for_item_table()),
                self.main_table_view_matches(old_self.powerpm@),
                self.list_area_view_matches(old_self.powerpm@),
                self.log_area_view_matches(old_self.powerpm@),
                self.tentative_main_table_valid(),
                self.tentative_main_table() == old_self.tentative_main_table(),
                self.tentative_item_table_valid(),
                self.tentative_item_table() == old_self.tentative_item_table(),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    condition(self.powerpm@.durable_state)
                }),
        {
            subregion.lemma_reveal_opaque_inv(&self.powerpm);

            let condition = old_self.condition_preserved_by_subregion_masks();
            let s = self.powerpm@.durable_state;
            assert(condition(s)) by {
                /*
                let s_old = lemma_get_crash_state_given_one_for_other_view_differing_only_where_subregion_allows(
                    self.powerpm@,
                    old_self.powerpm@,
                    s,
                    old_self.overall_metadata.item_table_addr as nat,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table()
                );
                */
                let s_old = s;
                assert(condition(s_old));
                assert(s_old.len() == s.len() == old_self.powerpm@.len());
                assert(memories_differ_only_where_subregion_allows(
                    s_old, s,
                    old_self.overall_metadata.item_table_addr as nat,
                    old_self.overall_metadata.item_table_size as nat,
                    old_self.get_writable_mask_for_item_table()
                ));
            }

//            lemma_persistent_memory_view_can_crash_as_committed(self.powerpm@);

            assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat));
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                      self.overall_metadata.list_area_size as nat));
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat) =~=
                   get_subregion_view(old_self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                      self.overall_metadata.log_area_size as nat));
            
            let old_tentative_state_bytes =
                apply_physical_log_entries(old_self.powerpm@.read_state, old_self.log@.physical_op_list).unwrap();
            let tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, old_self.log@.physical_op_list).unwrap();
            lemma_if_memories_differ_in_index_table_their_differences_commute_with_log_replay(
                old_self.powerpm@.read_state,
                self.powerpm@.read_state,
                self.log@.physical_op_list,
                self.overall_metadata
            );
            let old_tentative_main_table_bytes =
                extract_bytes(old_tentative_state_bytes, old_self.overall_metadata.main_table_addr as nat,
                                 old_self.overall_metadata.main_table_size as nat);
            let tentative_main_table_bytes =
                extract_bytes(tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            assert(tentative_main_table_bytes =~= old_tentative_main_table_bytes);
            let old_tentative_main_table_parsed =
                parse_main_table::<K>(old_tentative_main_table_bytes, old_self.overall_metadata.num_keys,
                                      old_self.overall_metadata.main_table_entry_size).unwrap();
            let tentative_main_table_parsed =
                parse_main_table::<K>(tentative_main_table_bytes, self.overall_metadata.num_keys,
                                      self.overall_metadata.main_table_entry_size).unwrap();
            assert(old_tentative_main_table_parsed.valid_item_indices() ==
                   tentative_main_table_parsed.valid_item_indices());
            let old_tentative_item_table_bytes =
                extract_bytes(old_tentative_state_bytes, self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let old_tentative_item_table_parsed =
                parse_item_table::<I, K>(old_tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         old_tentative_main_table_parsed.valid_item_indices());
            let tentative_item_table_bytes =
                extract_bytes(tentative_state_bytes, self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);
            let tentative_item_table_parsed =
                parse_item_table::<I, K>(tentative_item_table_bytes,
                                         self.overall_metadata.num_keys as nat,
                                         tentative_main_table_parsed.valid_item_indices());
            lemma_index_table_unaffected_by_log_replay(old_self.powerpm@.read_state, self.log@.physical_op_list,
                                                       self.overall_metadata);
            lemma_index_table_unaffected_by_log_replay(self.powerpm@.read_state, self.log@.physical_op_list,
                                                       self.overall_metadata);
            assert forall|addr: int| 0 <= addr < tentative_item_table_bytes.len() &&
                old_tentative_item_table_bytes[addr] != #[trigger] tentative_item_table_bytes[addr] implies
                address_belongs_to_invalid_item_table_entry::<I>(addr, self.overall_metadata.num_keys,
                                                                 tentative_main_table_parsed.valid_item_indices()) by {
                assert(address_belongs_to_invalid_item_table_entry::<I>(
                    addr,
                    old_self.overall_metadata.num_keys,
                    old_self.item_table.durable_valid_indices().union(old_self.item_table.tentative_valid_indices())
                ));
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                old_tentative_item_table_bytes,
                tentative_item_table_bytes,
                self.overall_metadata.num_keys,
                tentative_main_table_parsed.valid_item_indices(),
            );
            assert(tentative_item_table_parsed == old_tentative_item_table_parsed);
        }

        proof fn lemma_reestablish_inv_after_tentatively_write_item(
            self,
            old_self: Self,
            item_index: u64,
            item: I,
        )
            requires
                old_self.valid(),
                !old_self.transaction_committed(),
                self == (Self { item_table: self.item_table, powerpm: self.powerpm, ..old_self }),
                self.powerpm.inv(),
                self.powerpm.constants() == old_self.powerpm.constants(),
                views_differ_only_where_subregion_allows(old_self.powerpm@, self.powerpm@,
                                                         self.overall_metadata.item_table_addr as nat,
                                                         self.overall_metadata.item_table_size as nat,
                                                         old_self.get_writable_mask_for_item_table()),
                self.main_table_view_matches(old_self.powerpm@),
                self.list_area_view_matches(old_self.powerpm@),
                self.log_area_view_matches(old_self.powerpm@),
                ({
                    let condition = old_self.condition_preserved_by_subregion_masks();
                    condition(self.powerpm@.durable_state)
                }),
                self.item_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata),
                old_self.item_table.free_list().contains(item_index),
                self.item_table@.durable_item_table == old_self.item_table@.durable_item_table,
                
                forall |i: u64| 0 <= i < self.overall_metadata.num_keys && i != item_index ==>
                    #[trigger] self.item_table.outstanding_items[i] == old_self.item_table.outstanding_items[i],
                self.item_table.outstanding_items[item_index] == Some(OutstandingItem::Created(item)),
                self.main_table == old_self.main_table,
                self.tentative_main_table() == old_self.tentative_main_table(),
                // self.main_table@.valid_item_indices() == self.item_table.durable_valid_indices(),

                forall |other_index: u64| self.item_table.free_list().contains(other_index) <==>
                    old_self.item_table.free_list().contains(other_index) && other_index != item_index,
                deserialize_version_metadata(self.powerpm@.durable_state) == self.version_metadata,
                log_entries_do_not_modify_item_table(self.log@.physical_op_list, self.overall_metadata),
                log_entries_do_not_modify_free_main_table_entries(self.log@.physical_op_list,
                                                                  self.main_table.free_indices(),
                                                                  self.overall_metadata),
            ensures
                self.inv(),
                self.constants() == old_self.constants(),
                !self.transaction_committed(),
                forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==>
                    self.powerpm@.read_state[addr] == old_self.powerpm@.read_state[addr],
                forall|addr: int| 0 <= addr < VersionMetadata::spec_size_of() ==>
                    self.powerpm@.durable_state[addr] == old_self.powerpm@.durable_state[addr],
                forall|addr: int| self.version_metadata.overall_metadata_addr <= addr
                            < self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                    self.powerpm@.read_state[addr] == old_self.powerpm@.read_state[addr],
                forall|addr: int| self.version_metadata.overall_metadata_addr <= addr
                            < self.version_metadata.overall_metadata_addr + OverallMetadata::spec_size_of() ==>
                    self.powerpm@.durable_state[addr] == old_self.powerpm@.durable_state[addr],
                self.main_table_view_matches(old_self.powerpm@),
                self.list_area_view_matches(old_self.powerpm@),
                self.log_area_view_matches(old_self.powerpm@),
                self.tentative_main_table_valid(),
                self.tentative_item_table_valid(),
                self.tentative_main_table() == old_self.tentative_main_table(),
                self.tentative_item_table() == old_self.tentative_item_table(),
                ({
                    let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
                    let new_valid_item_indices = old_valid_item_indices.insert(item_index);
                    &&& self.tentative_hypothetical_item_table_valid(new_valid_item_indices)
                    &&& self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                           old_self.tentative_item_table().update(item_index as int, item)
                }),
        {
            let overall_metadata = self.overall_metadata;
            let log_area_addr = overall_metadata.log_area_addr;
            let log_area_size = overall_metadata.log_area_size;
            let region_size = overall_metadata.region_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let item_table_entry_size = I::spec_size_of() + u64::spec_size_of();
            
            assert(self.log.inv(self.powerpm@, self.version_metadata, overall_metadata)) by {
                assert(0 <= log_area_addr < log_area_addr + log_area_size <= region_size);
                assert(0 < spec_log_header_area_size() <= spec_log_area_pos() < log_area_size);
                self.log.lemma_same_op_log_view_preserves_invariant(old_self.powerpm, self.powerpm,
                    self.version_metadata, overall_metadata);
            }
            lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                old_self.powerpm@, self.powerpm@, self.version_metadata, overall_metadata
            );
            self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();

            let op_log = self.log@.physical_op_list;
            let old_tentative_bytes = apply_physical_log_entries(old_self.powerpm@.read_state, op_log);
            assert(old_tentative_bytes is Some);
            let old_tentative_bytes = old_tentative_bytes.unwrap();
            let old_tentative_kvstore_view =
                Self::physical_recover_after_applying_log(old_tentative_bytes, overall_metadata);
            assert(old_tentative_kvstore_view is Some);
            let old_tentative_kvstore_view = old_tentative_kvstore_view.unwrap();
            let old_tentative_main_table_bytes =
                extract_bytes(old_tentative_bytes, main_table_addr as nat, main_table_size as nat);
            let old_tentative_main_table_parsed =
                parse_main_table::<K>(old_tentative_main_table_bytes, num_keys,
                                      main_table_entry_size);
            assert(old_tentative_main_table_parsed is Some);
            let old_tentative_main_table_parsed = old_tentative_main_table_parsed.unwrap();
            let old_tentative_item_table_bytes =
                extract_bytes(old_tentative_bytes, item_table_addr as nat, item_table_size as nat);
            let old_tentative_item_table_parsed =
                parse_item_table::<I, K>(old_tentative_item_table_bytes, num_keys as nat,
                                         old_tentative_main_table_parsed.valid_item_indices());
            assert(old_tentative_item_table_parsed is Some);
            let old_tentative_item_table_parsed = old_tentative_item_table_parsed.unwrap();
            let old_durable_bytes = old_self.powerpm@.durable_state;
            let old_durable_main_table_bytes = extract_bytes(old_durable_bytes,
                                                             main_table_addr as nat,
                                                             main_table_size as nat);
            let old_durable_main_table_parsed = parse_main_table::<K>(old_durable_main_table_bytes,
                                                                      num_keys,
                                                                      main_table_entry_size);

            let old_current_main_table_region_view =
                get_subregion_view(old_self.powerpm@, main_table_addr as nat, main_table_size as nat);
            assert(old_current_main_table_region_view.durable_state == old_durable_main_table_bytes);
//            assert(old_current_main_table_region_view.can_crash_as(old_durable_main_table_bytes));
                                                                
            assert(old_durable_main_table_parsed is Some);
            let old_durable_main_table_parsed = old_durable_main_table_parsed.unwrap();

            assert(old_self.item_table.free_list().contains(item_index));
            assert(!old_tentative_main_table_parsed.valid_item_indices().contains(item_index));
            assert(!old_self.main_table@.valid_item_indices().contains(item_index));
            assert forall|idx: u64| idx < old_tentative_main_table_parsed.len() implies
                   (#[trigger] old_tentative_main_table_parsed.durable_main_table[idx as int] matches Some(e) ==>
                    e.entry.item_index != item_index) by {
            }

            lemma_if_memories_differ_in_index_table_their_differences_commute_with_log_replay(
                old_self.powerpm@.read_state,
                self.powerpm@.read_state,
                op_log,
                self.overall_metadata
            );
            
            let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state, op_log);
            assert(new_tentative_bytes is Some);
            let new_tentative_bytes = new_tentative_bytes.unwrap();
            let new_tentative_kvstore_view = Self::physical_recover_after_applying_log(
                new_tentative_bytes, overall_metadata);
            let new_tentative_main_table_bytes =
                extract_bytes(new_tentative_bytes, main_table_addr as nat, main_table_size as nat);
            assert(new_tentative_main_table_bytes =~= old_tentative_main_table_bytes) by {
                assert forall|addr: int| 0 <= addr < old_tentative_main_table_bytes.len() implies
                       #[trigger] new_tentative_main_table_bytes[addr] == old_tentative_main_table_bytes[addr] by {
                    assert(trigger_addr(main_table_addr + addr));
                }
            }
            let new_tentative_main_table_parsed =
                parse_main_table::<K>(new_tentative_main_table_bytes, num_keys,
                                      main_table_entry_size);
            assert(new_tentative_main_table_parsed is Some);
            let new_tentative_main_table_parsed = new_tentative_main_table_parsed.unwrap();
            assert(new_tentative_main_table_parsed == old_tentative_main_table_parsed);
            assert(!new_tentative_main_table_parsed.valid_item_indices().contains(item_index));

            let old_current_item_table_region_view =
                get_subregion_view(old_self.powerpm@, item_table_addr as nat, item_table_size as nat);
            let new_current_main_table_region_view =
                get_subregion_view(self.powerpm@, main_table_addr as nat, main_table_size as nat);
            let new_current_item_table_region_view =
                get_subregion_view(self.powerpm@, item_table_addr as nat, item_table_size as nat);
            let new_durable_bytes = self.powerpm@.read_state;
            let new_durable_item_table_bytes =
                extract_bytes(new_durable_bytes, item_table_addr as nat, item_table_size as nat);
            let new_tentative_item_table_bytes =
                extract_bytes(new_tentative_bytes, item_table_addr as nat, item_table_size as nat);
            assert(new_tentative_item_table_bytes =~= new_durable_item_table_bytes) by {
                assert forall|addr: int| 0 <= addr < new_durable_item_table_bytes.len() implies
                       #[trigger] new_tentative_item_table_bytes[addr] == new_durable_item_table_bytes[addr] by {
                    assert(trigger_addr(item_table_addr + addr));
                }
            }
            assert(new_tentative_main_table_parsed == old_tentative_main_table_parsed);

            let old_tentative_item_table_bytes =
                extract_bytes(old_tentative_bytes, item_table_addr as nat, item_table_size as nat);
            let old_durable_item_table_bytes =
                extract_bytes(old_durable_bytes, item_table_addr as nat, item_table_size as nat);
            assert(AbstractPhysicalOpLogEntry::log_inv(op_log, self.version_metadata, self.overall_metadata)) by {
                old_self.log.lemma_reveal_opaque_op_log_inv(old_self.powerpm, old_self.version_metadata,
                                                            old_self.overall_metadata);
            }
            let old_flushed_bytes = old_self.powerpm@.read_state;
            let old_flushed_item_table_bytes = extract_bytes(old_flushed_bytes, item_table_addr as nat,
                                                             item_table_size as nat);
            lemma_item_table_bytes_unchanged_by_applying_log_entries(
                old_flushed_bytes, op_log, old_self.version_metadata, old_self.overall_metadata
            );
            assert(old_tentative_item_table_bytes =~= old_flushed_item_table_bytes) by {
                assert(old_tentative_item_table_bytes.len() == old_flushed_item_table_bytes.len() == item_table_size);
                assert forall|addr: int| 0 <= addr < old_flushed_item_table_bytes.len() implies
                       #[trigger] old_tentative_item_table_bytes[addr] == old_flushed_item_table_bytes[addr] by {
                    let absolute_addr = item_table_addr + addr;
                    assert(item_table_addr <= absolute_addr < item_table_addr + item_table_size);
                    assert(old_tentative_bytes == apply_physical_log_entries(old_flushed_bytes, op_log).unwrap());
                    assert(old_flushed_bytes[absolute_addr] == old_tentative_bytes[absolute_addr]);
                }
            }

            let new_flushed_bytes = self.powerpm@.read_state;
            let new_flushed_item_table_bytes = extract_bytes(new_flushed_bytes, item_table_addr as nat,
                                                             item_table_size as nat);
            lemma_item_table_bytes_unchanged_by_applying_log_entries(
                new_flushed_bytes, op_log, self.version_metadata, self.overall_metadata
            );
            assert(new_tentative_item_table_bytes =~= new_flushed_item_table_bytes) by {
                assert(new_tentative_item_table_bytes.len() == new_flushed_item_table_bytes.len() == item_table_size);
                assert forall|addr: int| 0 <= addr < new_flushed_item_table_bytes.len() implies
                       #[trigger] new_tentative_item_table_bytes[addr] == new_flushed_item_table_bytes[addr] by {
                    let absolute_addr = item_table_addr + addr;
                    assert(item_table_addr <= absolute_addr < item_table_addr + item_table_size);
                    assert(new_tentative_bytes == apply_physical_log_entries(new_flushed_bytes, op_log).unwrap());
                    assert(new_flushed_bytes[absolute_addr] == new_tentative_bytes[absolute_addr]);
                }
            }
            
            assert forall|addr: int| {
                &&& 0 <= addr < new_flushed_item_table_bytes.len()
                &&& old_flushed_item_table_bytes[addr] != #[trigger] new_flushed_item_table_bytes[addr]
            } implies address_belongs_to_invalid_item_table_entry::<I>(
                addr, num_keys, new_tentative_main_table_parsed.valid_item_indices()
            ) by {
                let entry_size = (I::spec_size_of() + u64::spec_size_of()) as int;
                assert(old_flushed_item_table_bytes[addr] == old_self.powerpm@.read_state[addr + item_table_addr]);
                assert(new_flushed_item_table_bytes[addr] == self.powerpm@.read_state[addr + item_table_addr]);
                assert(address_belongs_to_invalid_item_table_entry::<I>(
                    addr,
                    num_keys,
                    old_self.item_table.durable_valid_indices().union(old_self.item_table.tentative_valid_indices())
                ));
                lemma_auto_addr_in_entry_divided_by_entry_size(item_index as nat, num_keys as nat, entry_size as nat);
                assert(trigger_addr(addr));
                let which_entry = addr / entry_size as int;
                if addr >= num_keys * entry_size {
                    assert(which_entry >= num_keys);
                    assert(false);
                }
                else {
                    assert(index_to_offset(which_entry as nat, entry_size as nat) <= addr <
                           index_to_offset(which_entry as nat, entry_size as nat) + entry_size);
                }
            }
            lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                old_flushed_item_table_bytes,
                new_flushed_item_table_bytes,
                num_keys,
                new_tentative_main_table_parsed.valid_item_indices(),
            );

            let new_tentative_item_table_parsed =
                parse_item_table::<I, K>(new_tentative_item_table_bytes, num_keys as nat,
                                         new_tentative_main_table_parsed.valid_item_indices()).unwrap();
            assert(new_tentative_item_table_parsed == old_tentative_item_table_parsed);

            let hypothetical_valid_item_indices =
                new_tentative_main_table_parsed.valid_item_indices().insert(item_index);
            let hypothetical_item_table_parsed =
                parse_item_table::<I, K>(new_tentative_item_table_bytes, num_keys as nat,
                                         hypothetical_valid_item_indices);
            assert forall|i: u64| i < num_keys && hypothetical_valid_item_indices.contains(i) implies {
                       &&& validate_item_table_entry::<I, K>(
                           #[trigger] extract_bytes(new_tentative_item_table_bytes,
                                                    index_to_offset(i as nat, item_table_entry_size as nat),
                                                    item_table_entry_size))
                       &&& parse_item_entry::<I, K>(
                           extract_bytes(new_tentative_item_table_bytes,
                                         index_to_offset(i as nat, item_table_entry_size as nat),
                                         item_table_entry_size)) ==
                          if i == item_index {
                              Some(item)
                          } else {
                              new_tentative_item_table_parsed.durable_item_table[i as int]
                          }
                   } by {
                if i == item_index {
                    let start = index_to_offset(i as nat, item_table_entry_size as nat);
                    let entry_bytes = extract_bytes(new_tentative_item_table_bytes,
                                                    start, item_table_entry_size);
                    lemma_valid_entry_index(i as nat, num_keys as nat, item_table_entry_size as nat);
                    assert(new_current_item_table_region_view.len() == item_table_size >=
                           index_to_offset(num_keys as nat, item_table_entry_size as nat));
                    assert(self.item_table.outstanding_items[i] is Some); // TODO: may need direct comparison to item
                    assert(old_self.item_table.outstanding_item_table_entry_matches_pm_view(
                        old_current_item_table_region_view, i
                    ));
                    assert(self.item_table.outstanding_item_table_entry_matches_pm_view(
                        new_current_item_table_region_view, i
                    ));
                    assert(outstanding_bytes_match(new_current_item_table_region_view, start as int,
                                                   spec_crc_bytes(I::spec_to_bytes(item))));
                    assert(outstanding_bytes_match(new_current_item_table_region_view,
                                                   start as int + u64::spec_size_of(), I::spec_to_bytes(item)));
                    broadcast use pmcopy_axioms;
                    lemma_outstanding_bytes_match_after_flush(new_current_item_table_region_view, start as int,
                                                              spec_crc_bytes(I::spec_to_bytes(item)));
                    lemma_outstanding_bytes_match_after_flush(new_current_item_table_region_view,
                                                              start as int + u64::spec_size_of(),
                                                              I::spec_to_bytes(item));
                    assert(new_durable_item_table_bytes == new_current_item_table_region_view.read_state)
                    by {
                        lemma_subregion_commutes_with_flush(self.powerpm@, item_table_addr as nat,
                                                            item_table_size as nat);
                    }
                    assert(extract_bytes(entry_bytes, 0, u64::spec_size_of()) =~=
                           spec_crc_bytes(I::spec_to_bytes(item)));
                    assert(extract_bytes(entry_bytes, u64::spec_size_of(), I::spec_size_of()) =~=
                           I::spec_to_bytes(item));
                    assert(validate_item_table_entry::<I, K>(entry_bytes));
                }
            }
            assert(validate_item_table_entries::<I, K>(new_tentative_item_table_bytes, num_keys as nat,
                                                       hypothetical_valid_item_indices));
            assert(hypothetical_item_table_parsed is Some);
            assert(self.tentative_hypothetical_item_table_valid(hypothetical_valid_item_indices));
            assert(self.tentative_hypothetical_item_table(hypothetical_valid_item_indices) =~=
                   old_self.tentative_item_table().update(item_index as int, item));
        }

        exec fn general_abort_after_failed_operation(
            &mut self,
            Ghost(pre_self): Ghost<Self>,
            Tracked(perm): Tracked<&Perm>,
        )
            requires 
                old(self).inv(),
                pre_self.inv(),
                !old(self).transaction_committed(),
                !pre_self.transaction_committed(),
                old(self).powerpm@.len() == pre_self.powerpm@.len(),
                ({
                    let main_table_subregion_view =
                        get_subregion_view(old(self).powerpm@, old(self).overall_metadata.main_table_addr as nat,
                                           old(self).overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(main_table_subregion_view.durable_state,
                                          old(self).overall_metadata.num_keys, 
                                          old(self).overall_metadata.main_table_entry_size) is Some
                }),
                old(self).main_table@ == pre_self.main_table@,
                old(self).item_table@ == pre_self.item_table@,
                old(self).durable_list@ == pre_self.durable_list@,
                old(self).log@ == pre_self.log@,
                old(self).version_metadata == pre_self.version_metadata,
                old(self).overall_metadata == pre_self.overall_metadata,
                no_outstanding_writes_to_version_metadata(old(self).powerpm@),
                no_outstanding_writes_to_version_metadata(pre_self.powerpm@),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm@, old(self).version_metadata.overall_metadata_addr as int),
                no_outstanding_writes_to_overall_metadata(pre_self.powerpm@, pre_self.version_metadata.overall_metadata_addr as int),
                old(self).item_table.durable_valid_indices() == old(self).main_table@.valid_item_indices(),
                forall |s| {
                    &&& Self::physical_recover(s, old(self).spec_version_metadata(),
                                             old(self).spec_overall_metadata()) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm@.durable_state)
                } ==> #[trigger] perm.check_permission(s),
                perm.check_permission(old(self).powerpm@.durable_state),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                self.tentative_view() ==
                    Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                    self.spec_overall_metadata(), AbstractOpLogState::initialize()),
                !self.transaction_committed(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                self.spec_version_metadata() == old(self).spec_version_metadata(),
                self@ == old(self)@,
                self.item_table@ == old(self).item_table@,
                self.durable_list@ == old(self).durable_list@,
                self.main_table@ == old(self).main_table@,
                self.powerpm@.flush_predicted(),
                self.tentative_view() == Some(self@),
                perm.check_permission(self.powerpm@.durable_state),
        {
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata,
                                                        self.overall_metadata);
//                lemma_persistent_memory_view_can_crash_as_committed(self.powerpm@);
            }

            let ghost mid_self = *self;
            self.log.abort_transaction(&mut self.powerpm, self.version_metadata, self.overall_metadata);
            
            let ghost main_table_subregion_view = get_subregion_view(self.powerpm@,
                                                                     self.overall_metadata.main_table_addr as nat,
                                                                     self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.powerpm@,
                                                                     self.overall_metadata.item_table_addr as nat,
                                                                     self.overall_metadata.item_table_size as nat);
            let ghost list_area_subregion_view = get_subregion_view(self.powerpm@,
                                                                    self.overall_metadata.list_area_addr as nat,
                                                                    self.overall_metadata.list_area_size as nat);
        
            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    mid_self.powerpm@,
                    self.powerpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(mid_self);  
                
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old(self).powerpm@.read_state, self.powerpm@.durable_state, self.version_metadata, self.overall_metadata);

                let old_main_table_subregion_view = get_subregion_view(old(self).powerpm@,
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion_view.read_state == old_main_table_subregion_view.read_state);

                assert({
                    let s = item_table_subregion_view.durable_state;
                    &&& parse_item_table::<I, K>(s, self.overall_metadata.num_keys as nat, self.item_table.durable_valid_indices())
                            matches Some(table_view)
                    &&& table_view.durable_item_table == self.item_table@.durable_item_table
                });
            }

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@),
                                                Ghost(self.overall_metadata));

            proof {
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old(self).powerpm@.read_state, self.powerpm@.durable_state, 
                    self.version_metadata, self.overall_metadata
                );

                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();

                let durable_state_bytes = self.powerpm@.durable_state;
                let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_item_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                
                let old_durable_main_table_subregion = get_subregion_view(old(self).powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                let old_durable_item_table_subregion = get_subregion_view(old(self).powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat);
                let durable_main_table_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                let durable_item_table_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_subregion.durable_state, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size);
                let tentative_state_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list);
        
                assert(tentative_state_bytes == Some(self.powerpm@.durable_state));
//                assert(old_durable_main_table_subregion.can_crash_as(old_durable_main_table_subregion.read_state));
                assert(durable_main_table_subregion.durable_state == old_durable_main_table_subregion.read_state);
                assert(durable_main_table_region == durable_main_table_subregion.durable_state);

                assert(durable_item_table_subregion.durable_state == old_durable_item_table_subregion.read_state);
                assert(durable_item_table_region == durable_item_table_subregion.durable_state);
                
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));
            }
        }

        exec fn abort_after_failed_op_log_operation(
            &mut self,
            Ghost(old_self): Ghost<Self>,
            Ghost(pre_self): Ghost<Self>,
            Tracked(perm): Tracked<&Perm>,
        )
            requires 
                old_self.inv(),
                pre_self.inv(),
                !old_self.transaction_committed(),
                !pre_self.transaction_committed(),
                !old(self).transaction_committed(),
                ({
                    let main_table_subregion_view = get_subregion_view(old(self).powerpm@, old(self).overall_metadata.main_table_addr as nat,
                        old(self).overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(main_table_subregion_view.durable_state, old(self).overall_metadata.num_keys, 
                        old(self).overall_metadata.main_table_entry_size) is Some
                }),
                old(self).powerpm.inv(),
                old(self).overall_metadata == pre_self.overall_metadata,
                pre_self.overall_metadata == old_self.overall_metadata,
                old(self).version_metadata == pre_self.version_metadata,
                pre_self.version_metadata == old_self.version_metadata,
                old(self).powerpm@.len() == pre_self.powerpm@.len() == old_self.powerpm@.len(),
                old(self).powerpm@.flush_predicted(),
                views_differ_only_in_log_region(pre_self.powerpm@, old(self).powerpm@,
                                                old(self).overall_metadata.log_area_addr as nat,
                                                old(self).overall_metadata.log_area_size as nat),
                UntrustedOpLog::<K, L>::recover(old(self).powerpm@.durable_state, old(self).version_metadata, 
                                                old(self).overall_metadata) == Some(AbstractOpLogState::initialize()),
                old(self).log@.physical_op_list.len() == 0,
                old(self).main_table.main_table_entry_size == old(self).overall_metadata.main_table_entry_size,
                old(self).main_table == pre_self.main_table,
                old(self).main_table@ == old_self.main_table@,
                old(self).item_table == pre_self.item_table,
                old(self).item_table@ == old_self.item_table@,
                old(self).durable_list@ == old_self.durable_list@,
                old(self).log.inv(old(self).powerpm@, old(self).version_metadata, old(self).overall_metadata),
                old(self)@ == old_self@,
                old(self).item_table.durable_valid_indices() == old(self).main_table@.valid_item_indices(),
                perm.check_permission(old(self).powerpm@.durable_state),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                self.spec_version_metadata() == old(self).spec_version_metadata(),
                !self.transaction_committed(),
                ({
                    let tentative_view = self.tentative_view();
                    &&& tentative_view == Self::physical_recover_given_log(self.powerpm_view().read_state, 
                            self.spec_overall_metadata(), AbstractOpLogState::initialize())
                    &&& tentative_view == Some(self@)
                }),
                self@ == old_self@,
                self.main_table@ == old_self.main_table@,
                self.item_table@ == old_self.item_table@,
                self.powerpm@.flush_predicted(),
                perm.check_permission(self.powerpm@.durable_state),
        {
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
//                lemma_persistent_memory_view_can_crash_as_committed(self.powerpm@);
            }

            // If the append failed, we need to abort the transaction and prove that the durable KV store as a whole
            // aborts the current transaction. The abort has already been initiated

            let ghost main_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);      
            let ghost item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat); 
            let ghost list_area_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    pre_self.powerpm@,
                    self.powerpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                self.lemma_transaction_abort(pre_self); 
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    pre_self.powerpm@.read_state, self.powerpm@.durable_state, self.version_metadata, self.overall_metadata);
            }          

            // Clear all pending updates tracked in volatile memory by the DurableKvStore itself
            self.pending_updates = Vec::new();
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            // abort the transaction in each component to re-establish their invariants
            self.main_table.abort_transaction(Ghost(main_table_subregion_view), Ghost(self.overall_metadata));
            self.item_table.abort_transaction(Ghost(item_table_subregion_view), Ghost(self.overall_metadata));
            self.durable_list.abort_transaction(Ghost(list_area_subregion_view), Ghost(self.main_table@), Ghost(self.overall_metadata));

            proof {
                assert(!self.transaction_committed());
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).powerpm@, self.powerpm@, self.version_metadata, self.overall_metadata
                );
                
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                
                let durable_state_bytes = self.powerpm@.durable_state;
                let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_item_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                // let durable_list_area_region = extract_bytes(durable_state_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);

                let old_durable_main_table_subregion = get_subregion_view(old(self).powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                let old_durable_item_table_subregion = get_subregion_view(old(self).powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat);
                // let old_durable_list_area_subregion = get_subregion_view(old(self).powerpm@, self.overall_metadata.list_area_addr as nat,
                //     self.overall_metadata.list_area_size as nat);
                let durable_main_table_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                // let durable_list_area_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                //     self.overall_metadata.list_area_size as nat);
                let durable_item_table_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                let durable_main_table_view = parse_main_table::<K>(durable_main_table_subregion.durable_state, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size);
                let tentative_state_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list);
        
                assert(tentative_state_bytes == Some(self.powerpm@.durable_state));
//                assert(old_durable_main_table_subregion.can_crash_as(old_durable_main_table_subregion.read_state));
                assert(durable_main_table_subregion.durable_state == old_durable_main_table_subregion.read_state);
                assert(durable_main_table_region == durable_main_table_subregion.durable_state);

                assert(durable_item_table_subregion.durable_state == old_durable_item_table_subregion.read_state);
                assert(durable_item_table_region == durable_item_table_subregion.durable_state);
                
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));
            }
        }

        #[verifier::rlimit(30)]
        proof fn lemma_helper_for_justify_validify_log_entry(
            self,
            old_self: Self,
            self_before_main_table_create: Self,
            main_table_subregion: PoWERPersistentMemorySubregion,
            main_table_index: u64,
            item_index: u64,
            list_node_index: u64,
            key: K,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.transaction_committed(),
                old_self.tentative_view() is Some,
                old_self.tentative_main_table().durable_main_table[main_table_index as int] is None,
                forall |s| {
                    &&& Self::physical_recover(s, old_self.spec_version_metadata(), old_self.spec_overall_metadata()) == Some(old_self@)
                    &&& version_and_overall_metadata_match_deserialized(s, old_self.powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old_self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old_self.powerpm_view(),
                                                          old_self.spec_overall_metadata_addr() as int),
                old_self.powerpm_view().len() >= VersionMetadata::spec_size_of(),
                log_entries_do_not_modify_free_main_table_entries(
                    old_self.log@.physical_op_list,
                    old_self.main_table.free_indices(),
                    old_self.overall_metadata
                ),
                main_table_subregion.start() == self.overall_metadata.main_table_addr,
                main_table_subregion.len() == self.overall_metadata.main_table_size,
                main_table_subregion.inv(&self.powerpm, perm),
                main_table_subregion.constants() == self_before_main_table_create.powerpm.constants(),
                main_table_subregion.initial_region_view() == self_before_main_table_create.powerpm@,
                main_table_subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_main_table(),
                condition_sufficient_to_create_powerpm_subregion(
                    self_before_main_table_create.powerpm@, perm,
                    self_before_main_table_create.overall_metadata.main_table_addr,
                    self_before_main_table_create.overall_metadata.main_table_size as nat,
                    self_before_main_table_create.get_writable_mask_for_main_table(),
                    self_before_main_table_create.condition_preserved_by_subregion_masks(),
                ),
                self_before_main_table_create.inv(),
                self_before_main_table_create.powerpm.constants() == old_self.powerpm.constants(),
                self_before_main_table_create.tentative_main_table().durable_main_table[main_table_index as int] is None,
                get_subregion_view(self_before_main_table_create.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat) ==
                    get_subregion_view(old_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat),
                get_subregion_view(self_before_main_table_create.powerpm@, self.overall_metadata.log_area_addr as nat,
                                   self.overall_metadata.log_area_size as nat) == 
                    get_subregion_view(old_self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                       self.overall_metadata.log_area_size as nat),
                ({
                    let tentative_state_bytes =
                        apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state,
                                                   self_before_main_table_create.log@.physical_op_list);
                    let tentative_main_table_bytes =
                        extract_bytes(tentative_state_bytes.unwrap(),
                                      self_before_main_table_create.overall_metadata.main_table_addr as nat,
                                      self_before_main_table_create.overall_metadata.main_table_size as nat);
                    let tentative_main_table =
                        parse_main_table::<K>(tentative_main_table_bytes,
                                              self_before_main_table_create.overall_metadata.num_keys,
                                              self_before_main_table_create.overall_metadata.main_table_entry_size);
                    &&& tentative_state_bytes is Some
                    &&& tentative_main_table == Some(self_before_main_table_create.main_table.tentative_view())
                }),
                log_entries_do_not_modify_free_main_table_entries(
                    self_before_main_table_create.log@.physical_op_list,
                    self_before_main_table_create.main_table.free_indices(),
                    self_before_main_table_create.overall_metadata
                ),
                self.main_table.inv(main_table_subregion.view(&self.powerpm), self.overall_metadata),
                self.main_table@.durable_main_table == self_before_main_table_create.main_table@.durable_main_table,
                self_before_main_table_create ==
                    (Self{ item_table: self_before_main_table_create.item_table,
                           powerpm: self_before_main_table_create.powerpm,
                           ..old_self }),
                self == (Self{ main_table: self.main_table, powerpm: self.powerpm, ..self_before_main_table_create }),
                forall|i: u64| 0 <= i < self.overall_metadata.num_keys && i != main_table_index ==>
                    self.main_table.outstanding_entries[i] ==
                        self_before_main_table_create.main_table.outstanding_entries[i],
                self_before_main_table_create.main_table.free_list().contains(main_table_index),
                self.main_table.free_list() ==
                    self_before_main_table_create.main_table.free_list().remove(main_table_index),
                self.main_table.outstanding_entry_write_matches_pm_view(
                    get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat),
                    main_table_index,
                    self.overall_metadata.main_table_entry_size
                ),
                forall|addr: int| {
                    let entry_size = self.overall_metadata.main_table_entry_size as nat;
                    let start = index_to_offset(main_table_index as nat, entry_size);
                    &&& #[trigger] trigger_addr(addr)
                    &&& 0 <= addr < self.overall_metadata.main_table_size
                    &&& !(start <= addr < start + entry_size)
                } ==> {
                    let old_pm_view = get_subregion_view(self_before_main_table_create.powerpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat);
                    let new_pm_view = get_subregion_view(self.powerpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat);
                    views_match_at_addr(old_pm_view, new_pm_view, addr)
                },
                self_before_main_table_create.tentative_main_table_valid(),
                item_index < self.overall_metadata.num_keys,
                ({
                    &&& self.main_table.outstanding_entries[main_table_index] matches Some(e)
                    &&& e.key == key
                    &&& e.entry.head == list_node_index
                    &&& e.entry.tail == list_node_index
                    &&& e.entry.length == 0
                    &&& e.entry.first_entry_offset == 0
                    &&& e.entry.item_index == item_index
                }),
                ({
                    let t = self_before_main_table_create.tentative_main_table().durable_main_table;
                    forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Some ==> t[i].unwrap().key != key
                }),
                !old_self.tentative_main_table().valid_item_indices().contains(item_index),
                self_before_main_table_create.tentative_item_table_valid(),
                self_before_main_table_create.tentative_item_table() == old_self.tentative_item_table(),
            ensures
                self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
                self.log.inv(old_self.powerpm@, self.version_metadata, self.overall_metadata),
                self.tentative_main_table_valid(),
                ({
                    let op_log = self.log@.physical_op_list;
                    &&& apply_physical_log_entries(self.powerpm@.read_state, op_log) is Some
                    &&& apply_physical_log_entries(self.powerpm@.read_state, op_log).unwrap().len() ==
                           self.powerpm@.len()
                    &&& apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state,
                                                 op_log) is Some
                }),
                get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).durable_state ==
                   extract_bytes(self.powerpm@.durable_state, self.overall_metadata.main_table_addr as nat,
                                 self.overall_metadata.main_table_size as nat),
                ({
                    let current_durable_main_table_view =
                    get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat);
                    let current_durable_main_table_parsed = parse_main_table::<K>(
                        current_durable_main_table_view.durable_state,
                        self.overall_metadata.num_keys,
                        self.overall_metadata.main_table_entry_size
                    );
                    let current_tentative_state_bytes =
                        apply_physical_log_entries(self.powerpm@.read_state,
                                                   self.log@.physical_op_list).unwrap();
                    let current_tentative_main_table_bytes =
                        extract_bytes(current_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat);
                    let main_table_entry_size = self.overall_metadata.main_table_entry_size;
                    let start = index_to_offset(main_table_index as nat, main_table_entry_size as nat);
                    let entry = self.main_table.outstanding_entries[main_table_index].unwrap().entry;
                    let entry_bytes = extract_bytes(current_tentative_main_table_bytes,
                                                    start, main_table_entry_size as nat);
                    let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
                    let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                    let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                       ListEntryMetadata::spec_size_of());
                    let key_bytes = extract_bytes(
                        entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                    );
                    let e = self.main_table.outstanding_entries[main_table_index].unwrap();
                    let metadata_bytes2 = ListEntryMetadata::spec_to_bytes(e.entry);
                    let key_bytes2 = K::spec_to_bytes(e.key);
                    let crc_bytes2 = spec_crc_bytes(metadata_bytes2 + key_bytes2);
                    &&& current_durable_main_table_parsed == Some(self.main_table@)
                    &&& extract_bytes(current_durable_main_table_view.read_state,
                                         (start + u64::spec_size_of() * 2) as nat, ListEntryMetadata::spec_size_of())
                           == metadata_bytes2
                    &&& extract_bytes(current_durable_main_table_view.read_state,
                                         (start + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of()) as nat,
                                         K::spec_size_of())
                           == key_bytes2
                    &&& extract_bytes(current_durable_main_table_view.read_state,
                                         (start + u64::spec_size_of()) as nat, u64::spec_size_of())
                           == crc_bytes2
                    &&& cdb_bytes == (CDB_FALSE as u64).spec_to_bytes()
                    &&& metadata_bytes == entry.spec_to_bytes()
                    &&& key_bytes == key.spec_to_bytes()
                    &&& crc_bytes == spec_crc_bytes(metadata_bytes + key_bytes)
                }),
                ({
                    let overall_metadata = self.overall_metadata;
                    let mem1 = old_self.powerpm@.read_state;
                    let mem2 = self.powerpm@.read_state;
                    let op_log = self.log@.physical_op_list;
                    let mem1_post = apply_physical_log_entries(mem1, op_log).unwrap();
                    let mem2_post = apply_physical_log_entries(mem2, op_log).unwrap();
                    &&& apply_physical_log_entries(mem1, op_log) is Some
                    &&& apply_physical_log_entries(mem2, op_log) is Some
                    &&& mem1_post.len() == mem2_post.len() == mem1.len()
                    &&& forall|addr: int| {
                            &&& #[trigger] trigger_addr(addr)
                            &&& overall_metadata.main_table_addr <= addr
                                < overall_metadata.main_table_addr + overall_metadata.main_table_size
                        } ==> {
                            let start = overall_metadata.main_table_addr +
                                        index_to_offset(main_table_index as nat,
                                                        overall_metadata.main_table_entry_size as nat);
                            let len = overall_metadata.main_table_entry_size;
                            mem2_post[addr] == if start <= addr < start + len { mem2[addr] } else { mem1_post[addr] }
                        }
                }),
                ({
                    let overall_metadata = self.overall_metadata;
                    let subregion_view = get_subregion_view(self.powerpm@, overall_metadata.main_table_addr as nat,
                                                            overall_metadata.main_table_size as nat);
                    let op_log = self.log@.physical_op_list;
                    let mem = self.powerpm@.read_state;
                    let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    let entry_bytes = extract_bytes(
                        main_table_region,
                        index_to_offset(main_table_index as nat, overall_metadata.main_table_entry_size as nat),
                        overall_metadata.main_table_entry_size as nat
                    );
                    let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                    let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                       ListEntryMetadata::spec_size_of());
                    let key_bytes = extract_bytes(
                        entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
                    let key = K::spec_from_bytes(key_bytes);
                    let entry = self.main_table.outstanding_entries[main_table_index].unwrap();
                    let item_index = entry.entry.item_index;
                    &&& mem.len() == overall_metadata.region_size
                    &&& self.main_table.inv(subregion_view, overall_metadata)
                    &&& parse_main_table::<K>(subregion_view.durable_state, overall_metadata.num_keys,
                                             overall_metadata.main_table_entry_size) == Some(self.main_table@)
                    &&& overall_metadata.main_table_size >=
                          overall_metadata.num_keys * overall_metadata.main_table_entry_size
                    &&& 0 <= main_table_index < self.main_table@.len()
                    &&& self.main_table@.durable_main_table[main_table_index as int] is None
                    &&& self.main_table.outstanding_entries[main_table_index] is Some
                    &&& log_entries_do_not_modify_free_main_table_entries(
                        self.log@.physical_op_list, self.main_table.free_indices(), overall_metadata
                    )
                    &&& apply_physical_log_entries(mem, op_log) is Some
                    &&& main_table_view is Some
                    // &&& main_table_view.unwrap().inv(overall_metadata)
                    &&& metadata_bytes == entry.entry.spec_to_bytes()
                    &&& key_bytes == entry.key.spec_to_bytes()
                    &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& key == entry.key
                    &&& metadata == entry.entry
                    &&& 0 <= metadata.item_index < overall_metadata.num_keys
                }),
                ({
                    let num_keys = self.overall_metadata.num_keys;
                    let main_table_entry_size = self.overall_metadata.main_table_entry_size;
                    let old_tentative_state_bytes =
                        apply_physical_log_entries(old_self.powerpm@.read_state,
                                                   old_self.log@.physical_op_list).unwrap();
                    let mem1 =
                        extract_bytes(old_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat);
                    let current_tentative_state_bytes =
                        apply_physical_log_entries(self.powerpm@.read_state,
                                                   self.log@.physical_op_list).unwrap();
                    let mem2 =
                        extract_bytes(current_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat);
                    let table1 =
                        parse_main_table::<K>(mem1, num_keys, main_table_entry_size).unwrap().durable_main_table;
                    let table2 =
                        parse_main_table::<K>(mem2, num_keys, main_table_entry_size).unwrap().durable_main_table;
                    &&& parse_main_table::<K>(mem1, num_keys, main_table_entry_size) is Some
                    &&& parse_main_table::<K>(mem2, num_keys, main_table_entry_size) is Some
                    &&& table2.len() == table1.len()
                    &&& table2[main_table_index as int] is None
                    &&& forall|i: int| 0 <= i < table2.len() && i != main_table_index ==> #[trigger] table2[i] == table1[i]
                }),
                get_subregion_view(self_before_main_table_create.powerpm@, self.overall_metadata.item_table_addr as nat,
                                   self.overall_metadata.item_table_size as nat) ==
                    get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                       self.overall_metadata.item_table_size as nat),
                self_before_main_table_create.main_table.free_indices().contains(main_table_index),
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
            hide(reverse_item_mapping_exists);
         
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let entry = self.main_table.outstanding_entries@[main_table_index].entry;

            let old_tentative_state_bytes =
                apply_physical_log_entries(old_self.powerpm@.read_state,
                                           old_self.log@.physical_op_list).unwrap();
            let old_tentative_main_table_bytes =
                extract_bytes(old_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let old_tentative_main_table_parsed = parse_main_table::<K>(old_tentative_main_table_bytes,
                                                                        num_keys, main_table_entry_size);
            let old_current_main_table_view =
                get_subregion_view(old_self.powerpm@, main_table_addr as nat, main_table_size as nat);
            let old_current_main_table_bytes =
                extract_bytes(old_self.powerpm@.durable_state, main_table_addr as nat, main_table_size as nat);
            let old_current_main_table_parsed = parse_main_table::<K>(old_current_main_table_bytes,
                                                                      num_keys, main_table_entry_size);

            let op_log = self.log@.physical_op_list;
            let mid_tentative_state_bytes = prove_unwrap(
                apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state, op_log)
            );
            let mid_tentative_main_table_bytes =
                extract_bytes(mid_tentative_state_bytes, main_table_addr as nat, main_table_size as nat);
            let mid_tentative_main_table = prove_unwrap(
                parse_main_table::<K>(mid_tentative_main_table_bytes, num_keys, main_table_entry_size)
            );
            let mid_tentative_item_table_bytes =
                extract_bytes(mid_tentative_state_bytes, item_table_addr as nat, item_table_size as nat);
            
            let current_tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state,
                                           self.log@.physical_op_list).unwrap();
            let current_tentative_main_table_bytes =
                extract_bytes(current_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let current_tentative_main_table_parsed = parse_main_table::<K>(
                current_tentative_main_table_bytes, num_keys, main_table_entry_size
            );
            let current_tentative_item_table_bytes =
                extract_bytes(current_tentative_state_bytes, self.overall_metadata.item_table_addr as nat,
                              self.overall_metadata.item_table_size as nat);

            let current_durable_main_table_view =
                get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat);
            let current_durable_main_table_parsed = parse_main_table::<K>(
                current_durable_main_table_view.durable_state,
                self.overall_metadata.num_keys,
                self.overall_metadata.main_table_entry_size
            );

            self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                self_before_main_table_create, main_table_subregion, perm
            );
            self.log.lemma_same_op_log_view_preserves_invariant(old_self.powerpm, self.powerpm, self.version_metadata,
                                                                self.overall_metadata);
            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
                self.powerpm@.read_state, self.version_metadata, self.overall_metadata,
                self.log@.physical_op_list
            );
            lemma_log_replay_preserves_size(self.powerpm@.read_state,
                                            self.log@.physical_op_list);
            lemma_log_replay_preserves_size(self_before_main_table_create.powerpm@.read_state,
                                            self.log@.physical_op_list);

            assert(mid_tentative_item_table_bytes =~= current_tentative_item_table_bytes) by {
                assert(extract_bytes(self_before_main_table_create.powerpm@.read_state,
                                     item_table_addr as nat, item_table_size as nat) =~=
                       extract_bytes(self.powerpm@.read_state,
                                     item_table_addr as nat, item_table_size as nat));
                lemma_item_table_bytes_unchanged_by_applying_log_entries(
                    self_before_main_table_create.powerpm@.read_state,
                    self.log@.physical_op_list,
                    self.version_metadata,
                    self.overall_metadata
                );
                lemma_item_table_bytes_unchanged_by_applying_log_entries(
                    self.powerpm@.read_state,
                    self.log@.physical_op_list,
                    self.version_metadata,
                    self.overall_metadata
                );
                assert(mid_tentative_item_table_bytes.len() == item_table_size);
                assert(current_tentative_item_table_bytes.len() == item_table_size);
                assert forall|addr| 0 <= addr < mid_tentative_item_table_bytes.len() implies
                       mid_tentative_item_table_bytes[addr] == current_tentative_item_table_bytes[addr] by {
                    let absolute_addr = addr + item_table_addr;
                    assert(item_table_addr <= absolute_addr < item_table_addr + item_table_size);
                    assert(mid_tentative_state_bytes[absolute_addr] ==
                           self_before_main_table_create.powerpm@.read_state[absolute_addr]);
                    assert(current_tentative_state_bytes[absolute_addr] ==
                           self.powerpm@.read_state[absolute_addr]);
                    assert(mid_tentative_state_bytes[absolute_addr] == current_tentative_state_bytes[absolute_addr]);
                }
            }

            // To tentatively validify a record, we need to obtain a log entry representing 
            // its validification and tentatively append it to the operation log.
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).durable_state =~=
                   extract_bytes(self.powerpm@.durable_state, self.overall_metadata.main_table_addr as nat,
                                 self.overall_metadata.main_table_size as nat));
            assert(current_durable_main_table_parsed == Some(self.main_table@));

            assert forall|addr: int| {
                let start = self.overall_metadata.main_table_addr +
                            index_to_offset(main_table_index as nat, main_table_entry_size as nat);
                &&& #[trigger] trigger_addr(addr)
                &&& self.overall_metadata.main_table_addr <= addr
                    < self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size
                &&& !(start <= addr < start + main_table_entry_size)
            } implies self.powerpm@.read_state[addr] == old_self.powerpm@.read_state[addr] by {
                let relative_addr = addr - self.overall_metadata.main_table_addr;
                assert(self.powerpm@.read_state[addr] ==
                       current_durable_main_table_view.read_state[relative_addr]);
                assert(old_self.powerpm@.read_state[addr] ==
                       old_current_main_table_view.read_state[relative_addr]);
                lemma_auto_addr_in_entry_divided_by_entry_size(main_table_index as nat,
                                                               self.overall_metadata.num_keys as nat,
                                                               main_table_entry_size as nat);
                assert(trigger_addr(relative_addr));
                let i = relative_addr / main_table_entry_size as int;
                assert(i != main_table_index);
            }

            assert(old_self.main_table.free_indices().contains(main_table_index)) by {
                reveal(MainTable::opaquable_inv);
            }
            lemma_if_memories_differ_in_free_main_table_entry_their_differences_commute_with_log_replay(
                old_self.powerpm@.read_state,
                self.powerpm@.read_state,
                self.log@.physical_op_list,
                old_self.main_table.free_indices(),
                main_table_index,
                self.overall_metadata
            );

            let start = index_to_offset(main_table_index as nat, main_table_entry_size as nat);
            assert forall|addr: int| {
                &&& #[trigger] trigger_addr(addr)
                &&& 0 <= addr < old_tentative_main_table_bytes.len()
                &&& !(start <= addr < start + main_table_entry_size)
            } implies current_tentative_main_table_bytes[addr] == old_tentative_main_table_bytes[addr] by {
                assert(trigger_addr(main_table_addr + addr));
            }

            let entry_bytes = extract_bytes(current_tentative_main_table_bytes, start, main_table_entry_size as nat);
            let cdb_bytes = extract_bytes(entry_bytes, 0, u64::spec_size_of());
            let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
            let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                               ListEntryMetadata::spec_size_of());
            let key_bytes = extract_bytes(
                entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
            );
            assert(forall|addr: int| #![trigger current_tentative_state_bytes[addr]] {
                       &&& trigger_addr(addr)
                       &&& main_table_addr <= addr < main_table_addr + main_table_size
                       &&& main_table_addr + start <= addr < main_table_addr + start + main_table_entry_size
                   } ==> current_tentative_state_bytes[addr] == self.powerpm@.read_state[addr]);
            lemma_valid_entry_index(main_table_index as nat, num_keys as nat, main_table_entry_size as nat);
            
            // broadcast use pmcopy_axioms;

            let e = self.main_table.outstanding_entries[main_table_index].unwrap();
            let metadata_bytes2 = ListEntryMetadata::spec_to_bytes(e.entry);
            let key_bytes2 = K::spec_to_bytes(e.key);
            let crc_bytes2 = spec_crc_bytes(metadata_bytes2 + key_bytes2);
            assert(extract_bytes(current_durable_main_table_view.read_state,
                                 (start + u64::spec_size_of() * 2) as nat, ListEntryMetadata::spec_size_of())
                   =~= metadata_bytes2) by { broadcast use pmcopy_axioms; }

            assert(extract_bytes(current_durable_main_table_view.read_state,
                                 (start + u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of()) as nat,
                                 K::spec_size_of())
                   =~= key_bytes2) by { broadcast use pmcopy_axioms; }
            assert(extract_bytes(current_durable_main_table_view.read_state,
                                 (start + u64::spec_size_of()) as nat, u64::spec_size_of())
                   =~= crc_bytes2) by { broadcast use pmcopy_axioms; }
            assert(cdb_bytes =~= (CDB_FALSE as u64).spec_to_bytes());
            assert(metadata_bytes =~= entry.spec_to_bytes());
            assert(key_bytes =~= key.spec_to_bytes());
            assert(crc_bytes =~= spec_crc_bytes(metadata_bytes + key_bytes));

            lemma_main_table_recovery_after_updating_entry::<K>(
                old_tentative_main_table_bytes,
                current_tentative_main_table_bytes,
                num_keys,
                main_table_entry_size,
                main_table_index,
                self.main_table.outstanding_entries[main_table_index].unwrap().entry,
                key
            );
            
            let table1 = parse_main_table::<K>(old_tentative_main_table_bytes, num_keys, main_table_entry_size).unwrap().durable_main_table;
            let table2 = parse_main_table::<K>(current_tentative_main_table_bytes, num_keys, main_table_entry_size).unwrap().durable_main_table;
            assert(table1 == old_self.tentative_main_table().durable_main_table);
            assert(table2 == self.tentative_main_table().durable_main_table);

            assert(0 <= e.entry.item_index < overall_metadata.num_keys);
            
            assert(self.tentative_main_table_valid());

            assert(log_entries_do_not_modify_free_main_table_entries(self.log@.physical_op_list,
                                                                     self.main_table.free_indices(),
                                                                     overall_metadata)) by {
                assert forall|free_index: u64| #[trigger] self.main_table.free_indices().contains(free_index) implies
                           log_entries_do_not_modify_free_main_table_entry(self.log@.physical_op_list, free_index,
                                                                           overall_metadata) by {
                    assert(self_before_main_table_create.main_table.free_indices().contains(free_index));
                    assert(log_entries_do_not_modify_free_main_table_entry(
                        self_before_main_table_create.log@.physical_op_list,
                        free_index,
                        overall_metadata
                    ));
                }
            }

            // required to prove postcondition; we only bring it in at the end
            // to avoid instantiating too many unnecessary triggers
            broadcast use pmcopy_axioms; 
        }

        #[verifier::rlimit(20)]
        proof fn lemma_justify_validify_log_entry(
            self,
            old_self: Self,
            self_before_main_table_create: Self,
            main_table_subregion: PoWERPersistentMemorySubregion,
            main_table_index: u64,
            item_index: u64,
            list_node_index: u64,
            key: K,
            item: I,
            perm: &Perm,
        )
            requires
                old_self.inv(),
                !old_self.transaction_committed(),
                old_self.tentative_view() is Some,
                old_self.tentative_main_table().durable_main_table[main_table_index as int] is None,
                forall |s| {
                    &&& Self::physical_recover(s, old_self.spec_version_metadata(), old_self.spec_overall_metadata()) == Some(old_self@)
                    &&& version_and_overall_metadata_match_deserialized(s, old_self.powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old_self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old_self.powerpm_view(),
                                                          old_self.spec_overall_metadata_addr() as int),
                old_self.powerpm_view().len() >= VersionMetadata::spec_size_of(),
                log_entries_do_not_modify_free_main_table_entries(
                    old_self.log@.physical_op_list,
                    old_self.main_table.free_indices(),
                    old_self.overall_metadata
                ),
                main_table_subregion.start() == self.overall_metadata.main_table_addr,
                main_table_subregion.len() == self.overall_metadata.main_table_size,
                main_table_subregion.inv(&self.powerpm, perm),
                main_table_subregion.constants() == self_before_main_table_create.powerpm.constants(),
                main_table_subregion.initial_region_view() == self_before_main_table_create.powerpm@,
                main_table_subregion.is_writable_absolute_addr_fn() == old_self.get_writable_mask_for_main_table(),
                condition_sufficient_to_create_powerpm_subregion(
                    self_before_main_table_create.powerpm@, perm,
                    self_before_main_table_create.overall_metadata.main_table_addr,
                    self_before_main_table_create.overall_metadata.main_table_size as nat,
                    self_before_main_table_create.get_writable_mask_for_main_table(),
                    self_before_main_table_create.condition_preserved_by_subregion_masks(),
                ),
                self_before_main_table_create.inv(),
                self_before_main_table_create.powerpm.constants() == old_self.powerpm.constants(),
                get_subregion_view(self_before_main_table_create.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat) ==
                    get_subregion_view(old_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat),
                get_subregion_view(self_before_main_table_create.powerpm@, self.overall_metadata.log_area_addr as nat,
                                   self.overall_metadata.log_area_size as nat) == 
                    get_subregion_view(old_self.powerpm@, self.overall_metadata.log_area_addr as nat,
                                       self.overall_metadata.log_area_size as nat),
                ({
                    let tentative_state_bytes =
                        apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state,
                                                   self_before_main_table_create.log@.physical_op_list);
                    let tentative_main_table_bytes =
                        extract_bytes(tentative_state_bytes.unwrap(),
                                      self_before_main_table_create.overall_metadata.main_table_addr as nat,
                                      self_before_main_table_create.overall_metadata.main_table_size as nat);
                    let tentative_main_table =
                        parse_main_table::<K>(tentative_main_table_bytes,
                                              self_before_main_table_create.overall_metadata.num_keys,
                                              self_before_main_table_create.overall_metadata.main_table_entry_size);
                    &&& tentative_state_bytes is Some
                    &&& tentative_main_table == Some(self_before_main_table_create.main_table.tentative_view())
                }),
                self.main_table.inv(main_table_subregion.view(&self.powerpm), self.overall_metadata),
                self.main_table@.durable_main_table == self_before_main_table_create.main_table@.durable_main_table,
                views_differ_only_where_subregion_allows(
                    self_before_main_table_create.powerpm@,
                    self.powerpm@,
                    self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat,
                    self_before_main_table_create.get_writable_mask_for_main_table()
                ),
                self_before_main_table_create ==
                    (Self{ item_table: self_before_main_table_create.item_table,
                           powerpm: self_before_main_table_create.powerpm,
                           ..old_self }),
                self == (Self{ main_table: self.main_table, powerpm: self.powerpm, ..self_before_main_table_create }),
                forall|i: u64| 0 <= i < self.overall_metadata.num_keys && i != main_table_index ==>
                    self.main_table.outstanding_entries[i] ==
                        self_before_main_table_create.main_table.outstanding_entries[i],
                self_before_main_table_create.main_table.free_list().contains(main_table_index),
                self.main_table.free_list() ==
                    self_before_main_table_create.main_table.free_list().remove(main_table_index),
                self_before_main_table_create.tentative_main_table_valid(),
                self.main_table.outstanding_entry_write_matches_pm_view(
                    get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                       self.overall_metadata.main_table_size as nat),
                    main_table_index,
                    self.overall_metadata.main_table_entry_size
                ),
                forall|addr: int| {
                    let entry_size = self.overall_metadata.main_table_entry_size as nat;
                    let start = index_to_offset(main_table_index as nat, entry_size);
                    &&& #[trigger] trigger_addr(addr)
                    &&& 0 <= addr < self.overall_metadata.main_table_size
                    &&& !(start <= addr < start + entry_size)
                } ==> {
                    let old_pm_view = get_subregion_view(self_before_main_table_create.powerpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat);
                    let new_pm_view = get_subregion_view(self.powerpm@,
                                                         self.overall_metadata.main_table_addr as nat,
                                                         self.overall_metadata.main_table_size as nat);
                    views_match_at_addr(old_pm_view, new_pm_view, addr)
                },
                self_before_main_table_create.tentative_main_table().durable_main_table[main_table_index as int] is None,
                item_index < self.overall_metadata.num_keys,
                ({
                    &&& self.main_table.outstanding_entries[main_table_index] matches Some(e)
                    &&& e.key == key
                    &&& e.entry.head == list_node_index
                    &&& e.entry.tail == list_node_index
                    &&& e.entry.length == 0
                    &&& e.entry.first_entry_offset == 0
                    &&& e.entry.item_index == item_index
                }),
                ({
                    let t = self_before_main_table_create.tentative_main_table().durable_main_table;
                    forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Some ==> t[i].unwrap().key != key
                }),
                !old_self.tentative_main_table().valid_item_indices().contains(item_index),
                self_before_main_table_create.tentative_main_table() == old_self.tentative_main_table(),
                self_before_main_table_create.tentative_item_table_valid(),
                self_before_main_table_create.tentative_item_table() == old_self.tentative_item_table(),
                old_self.tentative_item_table_valid(),
                ({
                    let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
                    let new_valid_item_indices = old_valid_item_indices.insert(item_index);
                    &&& self_before_main_table_create.tentative_hypothetical_item_table_valid(new_valid_item_indices)
                    &&& self_before_main_table_create.tentative_hypothetical_item_table(new_valid_item_indices) ==
                           old_self.tentative_item_table().update(item_index as int, item)
                }),
            ensures
                self.inv(),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) ==
                    Some(self@),
                self.tentative_main_table() == self_before_main_table_create.tentative_main_table(),
                ({
                    let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
                    let new_valid_item_indices = old_valid_item_indices.insert(item_index);
                    &&& self.tentative_hypothetical_item_table_valid(new_valid_item_indices)
                    &&& self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                           old_self.tentative_item_table().update(item_index as int, item)
                }),
                ({
                    let overall_metadata = self.overall_metadata;
                    let subregion_view = get_subregion_view(self.powerpm@, overall_metadata.main_table_addr as nat,
                                                            overall_metadata.main_table_size as nat);
                    let op_log = self.log@.physical_op_list;
                    let mem = self.powerpm@.read_state;
                    let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                    let main_table_region = extract_bytes(current_tentative_state, 
                        overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                    let main_table_view = parse_main_table::<K>(main_table_region,
                        overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                    let entry_bytes = extract_bytes(
                        main_table_region,
                        index_to_offset(main_table_index as nat, overall_metadata.main_table_entry_size as nat),
                        overall_metadata.main_table_entry_size as nat
                    );
                    let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                    let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                       ListEntryMetadata::spec_size_of());
                    let key_bytes = extract_bytes(
                        entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                    );
                    let crc = u64::spec_from_bytes(crc_bytes);
                    let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
                    let key = K::spec_from_bytes(key_bytes);
                    let entry = self.main_table.outstanding_entries[main_table_index].unwrap();
                    let item_index = entry.entry.item_index;
                    &&& mem.len() == overall_metadata.region_size
                    &&& self.main_table.inv(subregion_view, overall_metadata)
                    &&& parse_main_table::<K>(subregion_view.durable_state, overall_metadata.num_keys,
                                             overall_metadata.main_table_entry_size) == Some(self.main_table@)
                    &&& overall_metadata.main_table_size >=
                          overall_metadata.num_keys * overall_metadata.main_table_entry_size
                    &&& 0 <= main_table_index < self.main_table@.len()
                    &&& self.main_table@.durable_main_table[main_table_index as int] is None
                    &&& self.main_table.outstanding_entries[main_table_index] is Some
                    &&& log_entries_do_not_modify_free_main_table_entries(op_log, self.main_table.free_indices(),
                                                                        overall_metadata)
                    &&& apply_physical_log_entries(mem, op_log) is Some
                    &&& main_table_view is Some
                    // &&& main_table_view.unwrap().inv(overall_metadata)
                    &&& metadata_bytes == entry.entry.spec_to_bytes()
                    &&& key_bytes == entry.key.spec_to_bytes()
                    &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                    &&& u64::bytes_parseable(crc_bytes)
                    &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                    &&& K::bytes_parseable(key_bytes)
                    &&& key == entry.key
                    &&& metadata == entry.entry
                    &&& 0 <= metadata.item_index < overall_metadata.num_keys
                    &&& !main_table_view.unwrap().valid_item_indices().contains(item_index)
                    &&& forall|i| 0 <= i < overall_metadata.num_keys &&
                           #[trigger] main_table_view.unwrap().durable_main_table[i] is Some
                           ==> main_table_view.unwrap().durable_main_table[i].unwrap().key != entry.key
                }),
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
         
            assert({
                &&& self.version_metadata == deserialize_version_metadata(self.powerpm@.durable_state)
                &&& self.version_metadata == deserialize_version_metadata(self.powerpm@.read_state)
                &&& self.overall_metadata == deserialize_overall_metadata(self.powerpm@.durable_state,
                                                                        self.version_metadata.overall_metadata_addr)
                &&& self.overall_metadata == deserialize_overall_metadata(self.powerpm@.read_state,
                                                                        self.version_metadata.overall_metadata_addr)
            }) by {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    self_before_main_table_create.powerpm@,
                    self.powerpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
            }
            
            self.lemma_helper_for_justify_validify_log_entry(old_self, self_before_main_table_create,
                                                             main_table_subregion, main_table_index, item_index,
                                                             list_node_index, key, perm);
            
            let overall_metadata = self.overall_metadata;
            let num_keys = overall_metadata.num_keys;
            let main_table_entry_size = overall_metadata.main_table_entry_size;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let entry = self.main_table.outstanding_entries@[main_table_index].entry;

            let old_tentative_state_bytes =
                apply_physical_log_entries(old_self.powerpm@.read_state,
                                           old_self.log@.physical_op_list).unwrap();
            let old_tentative_main_table_bytes =
                extract_bytes(old_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let old_tentative_main_table_parsed = parse_main_table::<K>(old_tentative_main_table_bytes,
                                                                        num_keys, main_table_entry_size);
            let old_current_main_table_view =
                get_subregion_view(old_self.powerpm@, main_table_addr as nat, main_table_size as nat);
            let old_current_main_table_bytes =
                extract_bytes(old_self.powerpm@.durable_state, main_table_addr as nat, main_table_size as nat);
            let old_current_main_table_parsed = parse_main_table::<K>(old_current_main_table_bytes,
                                                                      num_keys, main_table_entry_size);

            let op_log = self.log@.physical_op_list;
            let mid_tentative_state_bytes = prove_unwrap(
                apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state, op_log)
            );
            let mid_tentative_main_table_bytes =
                extract_bytes(mid_tentative_state_bytes, main_table_addr as nat, main_table_size as nat);
            let mid_tentative_main_table_parsed = prove_unwrap(
                parse_main_table::<K>(mid_tentative_main_table_bytes, num_keys, main_table_entry_size)
            );
            
            let current_tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state,
                                           self.log@.physical_op_list).unwrap();
            let current_tentative_main_table_bytes =
                extract_bytes(current_tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                              self.overall_metadata.main_table_size as nat);
            let current_tentative_main_table_parsed = prove_unwrap(
                parse_main_table::<K>(current_tentative_main_table_bytes, num_keys, main_table_entry_size)
            );
                
            let current_durable_main_table_view =
                get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                   self.overall_metadata.main_table_size as nat);
            let current_durable_main_table_parsed = parse_main_table::<K>(
                current_durable_main_table_view.durable_state,
                self.overall_metadata.num_keys,
                self.overall_metadata.main_table_entry_size
            );

            assert(old_tentative_main_table_parsed is Some);
            let old_tentative_main_table_parsed = old_tentative_main_table_parsed.unwrap();
            assert(old_current_main_table_parsed == Some(old_self.main_table@)) by {
                let s = extract_bytes(old_self.powerpm@.durable_state, main_table_addr as nat, main_table_size as nat);
            }
            let old_current_main_table_parsed = old_current_main_table_parsed.unwrap();

            self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                self_before_main_table_create, main_table_subregion, perm
            );

            assert forall|addr: int| {
                let start = main_table_addr + index_to_offset(main_table_index as nat, main_table_entry_size as nat);
                let len = main_table_entry_size;
                &&& #[trigger] trigger_addr(addr)
                &&& main_table_addr <= addr < main_table_addr + main_table_size
                &&& !(start <= addr < start + len)
            } implies self_before_main_table_create.powerpm@.read_state[addr] ==
                      self.powerpm@.read_state[addr] by {
                let mem1 = self_before_main_table_create.powerpm@.read_state;
                let mem2 = self.powerpm@.read_state;
                let relative_addr = addr - main_table_addr;
                lemma_auto_addr_in_entry_divided_by_entry_size(main_table_index as nat, num_keys as nat,
                                                               main_table_entry_size as nat);
                assert(trigger_addr(relative_addr));
                let which_entry = (relative_addr / main_table_entry_size as int) as u64;
                if relative_addr >= index_to_offset(num_keys as nat, main_table_entry_size as nat) {
                    assert(which_entry >= num_keys);
                    assert(!old_self.get_writable_mask_for_main_table()(addr));
                    assert(!main_table_subregion.is_writable_absolute_addr_fn()(addr));
                    assert(mem1[addr] == mem2[addr]);
                }
                else {
                    assert(index_to_offset(which_entry as nat, main_table_entry_size as nat) <= relative_addr <
                           index_to_offset(which_entry as nat, main_table_entry_size as nat) + main_table_entry_size);
                    assert(which_entry != main_table_index);
                    assert(self.main_table.outstanding_entries[which_entry] ==
                           self_before_main_table_create.main_table.outstanding_entries[which_entry]);
                    broadcast use pmcopy_axioms;
                    assert(self_before_main_table_create.powerpm@.durable_state[addr] ==
                           get_subregion_view(self_before_main_table_create.powerpm@, main_table_addr as nat,
                                              main_table_size as nat).durable_state[addr - main_table_addr]);
                    assert(self.powerpm@.durable_state[addr] ==
                           get_subregion_view(self.powerpm@, main_table_addr as nat,
                                              main_table_size as nat).durable_state[addr - main_table_addr]);
                }
            }

            lemma_if_memories_differ_in_free_main_table_entry_their_differences_commute_with_log_replay(
                self_before_main_table_create.powerpm@.read_state,
                self.powerpm@.read_state,
                self.log@.physical_op_list,
                self_before_main_table_create.main_table.free_indices(),
                main_table_index,
                self.overall_metadata
            );

            assert forall|addr: int| {
                let start = index_to_offset(main_table_index as nat, main_table_entry_size as nat);
                &&& #[trigger] trigger_addr(addr)
                &&& 0 <= addr < mid_tentative_main_table_bytes.len()
                &&& !(start <= addr < start + main_table_entry_size)
            } implies mid_tentative_main_table_bytes[addr] == current_tentative_main_table_bytes[addr] by {
                let absolute_addr = main_table_addr + addr;
                assert(trigger_addr(absolute_addr));
                lemma_log_replay_preserves_size(self_before_main_table_create.powerpm@.read_state, op_log);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, op_log);
                assert(mid_tentative_main_table_bytes[addr] ==
                       apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state,
                                                  op_log).unwrap()[absolute_addr]);
                assert(current_tentative_main_table_bytes[addr] ==
                       apply_physical_log_entries(self.powerpm@.read_state, op_log).unwrap()[absolute_addr]);
            }
            
            lemma_main_table_recovery_after_updating_entry::<K>(
                mid_tentative_main_table_bytes,
                current_tentative_main_table_bytes,
                num_keys,
                main_table_entry_size,
                main_table_index,
                entry,
                key
            );

            assert(mid_tentative_main_table_parsed.durable_main_table[main_table_index as int] is None);
            assert(mid_tentative_main_table_parsed =~= current_tentative_main_table_parsed);

            assert(!current_tentative_main_table_parsed.valid_item_indices().contains(item_index));
            assert forall|i| 0 <= i < num_keys &&
                       #[trigger] current_tentative_main_table_parsed.durable_main_table[i] is Some
                       implies current_tentative_main_table_parsed.durable_main_table[i].unwrap().key != key by {
                let table1 = mid_tentative_main_table_parsed.durable_main_table;
                let table2 = current_tentative_main_table_parsed.durable_main_table;
                assert(i != main_table_index);
                assert(table2[i] == table1[i]);
                assert(self_before_main_table_create.tentative_main_table().durable_main_table[i].unwrap().key != key);
            }

            let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
            let new_valid_item_indices = old_valid_item_indices.insert(item_index);

            let old_tentative_state_bytes =
                apply_physical_log_entries(self_before_main_table_create.powerpm@.read_state,
                                           self_before_main_table_create.log@.physical_op_list).unwrap();
            let old_tentative_item_table_bytes =
                extract_bytes(old_tentative_state_bytes, item_table_addr as nat,
                              item_table_size as nat);
            let new_tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list).unwrap();
            let new_tentative_item_table_bytes =
                extract_bytes(new_tentative_state_bytes, item_table_addr as nat,
                              item_table_size as nat);
            assert(new_tentative_item_table_bytes =~= old_tentative_item_table_bytes) by {
                assert forall|i: int| 0 <= i < new_tentative_item_table_bytes.len() implies
                    new_tentative_item_table_bytes[i] == old_tentative_item_table_bytes[i] by {
                    assert(new_tentative_item_table_bytes[i] ==
                           new_tentative_state_bytes[i + item_table_addr]);
                    assert(old_tentative_item_table_bytes[i] ==
                           old_tentative_state_bytes[i + item_table_addr]);
                    assert(new_tentative_state_bytes[i + item_table_addr] ==
                           self.powerpm@.read_state[i + item_table_addr]) by {
                        self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata,
                                                                self.overall_metadata);
                        lemma_item_table_bytes_unchanged_by_applying_log_entries(
                            self.powerpm@.read_state,
                            self.log@.physical_op_list,
                            self.version_metadata,
                            self.overall_metadata
                        );
                    }
                    assert(old_tentative_state_bytes[i + item_table_addr] ==
                           self_before_main_table_create.powerpm@.read_state[i + item_table_addr]) by {
                        self_before_main_table_create.log.lemma_reveal_opaque_op_log_inv(
                            self_before_main_table_create.powerpm, self_before_main_table_create.version_metadata,
                            self_before_main_table_create.overall_metadata);
                        lemma_item_table_bytes_unchanged_by_applying_log_entries(
                            self_before_main_table_create.powerpm@.read_state,
                            self_before_main_table_create.log@.physical_op_list,
                            self_before_main_table_create.version_metadata,
                            self_before_main_table_create.overall_metadata
                        );
                    }
                    assert(self_before_main_table_create.powerpm@.durable_state[i + item_table_addr] ==
                           self.powerpm@.durable_state[i + item_table_addr]);
                }
            }
            assert(self.tentative_hypothetical_item_table_valid(new_valid_item_indices));
            assert(self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                   self_before_main_table_create.tentative_hypothetical_item_table(new_valid_item_indices));
        }

        proof fn lemma_helper_for_finalize_tentative_create(
            self,
            old_self: Self,
            pre_append_self: Self,
            key: K,
            item: I,
            main_table_index: u64,
            item_index: u64,
            log_entry: PhysicalOpLogEntry,
        )
        requires
            old_self.valid(),
            // old_self.pending_alloc_inv(),
            old_self.tentative_item_table_valid(),
            pre_append_self.inv(),
            ({
                let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
                let new_valid_item_indices = old_valid_item_indices.insert(item_index);
                &&& pre_append_self.tentative_hypothetical_item_table_valid(new_valid_item_indices)
                &&& pre_append_self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                    old_self.tentative_item_table().update(item_index as int, item)
            }),
            self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
            log_entry@.inv(self.version_metadata, self.overall_metadata),
            self.log@ == pre_append_self.log@.tentatively_append_log_entry(log_entry@),
            log_entry_does_not_modify_free_main_table_entries(log_entry@, self.main_table.free_indices(),
                                                              self.overall_metadata),
            self.powerpm.inv(),
            pre_append_self.powerpm@.len() == self.powerpm@.len() == self.overall_metadata.region_size,
            pre_append_self.tentative_main_table() == old_self.tentative_main_table(),
            views_differ_only_in_log_region(pre_append_self.powerpm@, self.powerpm@,
                                            self.overall_metadata.log_area_addr as nat,
                                            self.overall_metadata.log_area_size as nat),
            log_entry_does_not_modify_addresses(log_entry@, self.overall_metadata.item_table_addr as nat,
                                                self.overall_metadata.item_table_size as nat),
            log_entry.absolute_addr + log_entry.len <= self.powerpm@.len(),
            pre_append_self.version_metadata == old_self.version_metadata,
            pre_append_self.overall_metadata == old_self.overall_metadata,
            self.version_metadata == old_self.version_metadata,
            self.overall_metadata == old_self.overall_metadata,
            main_table_index < self.overall_metadata.num_keys,
            pre_append_self.main_table.tentative_view().durable_main_table[main_table_index as int] ==
                Some(MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            pre_append_self.main_table.tentative_view().durable_main_table[main_table_index as int] == 
                Some(MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            log_entries_do_not_modify_item_table(pre_append_self.log@.physical_op_list,
                                                 pre_append_self.overall_metadata),
            !pre_append_self.log@.op_list_committed,
            pre_append_self.main_table.tentative_view() ==
                old_self.main_table.tentative_view().update(
                    main_table_index as int,
                    MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            pre_append_self.item_table.tentative_view() ==
                old_self.item_table.tentative_view().update(item_index as int, item),
            pre_append_self.main_table.tentative_view().valid_item_indices() ==
                old_self.main_table.tentative_view().valid_item_indices().insert(item_index),
            pre_append_self.item_table.tentative_valid_indices() ==
                old_self.item_table.tentative_valid_indices().insert(item_index),
            !self.log@.op_list_committed,
            self.pending_updates@ == pre_append_self.pending_updates@.push(log_entry),
            self == (Self{ powerpm: self.powerpm, log: self.log, pending_updates: self.pending_updates, ..pre_append_self }),
            ({
                let mem = pre_append_self.powerpm@.read_state;
                let op_log = pre_append_self.log@.physical_op_list;
                let overall_metadata = self.overall_metadata;
                let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                let main_table_region = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let main_table_view = parse_main_table::<K>(main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                let new_mem = apply_physical_log_entry(current_tentative_state, log_entry@);
                let new_main_table_region = extract_bytes(new_mem.unwrap(), 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                let entry_bytes = extract_bytes(
                    main_table_region,
                    index_to_offset(main_table_index as nat, overall_metadata.main_table_entry_size as nat),
                    overall_metadata.main_table_entry_size as nat
                );
                let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                   ListEntryMetadata::spec_size_of());
                let key_bytes = extract_bytes(
                    entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                );
                let crc = u64::spec_from_bytes(crc_bytes);
                let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
                let key = K::spec_from_bytes(key_bytes);
                let entry = pre_append_self.main_table.outstanding_entries@[main_table_index];
                let item_index = entry.entry.item_index;
                &&& apply_physical_log_entries(mem, op_log) is Some
                &&& pre_append_self.main_table.outstanding_entries[main_table_index] is Some
                &&& main_table_view is Some
                &&& main_table_view.unwrap().inv(overall_metadata)
                &&& forall|i| 0 <= i < overall_metadata.num_keys &&
                       #[trigger] main_table_view.unwrap().durable_main_table[i] is Some
                       ==> main_table_view.unwrap().durable_main_table[i].unwrap().key != entry.key
                &&& metadata_bytes == entry.entry.spec_to_bytes()
                &&& key_bytes == entry.key.spec_to_bytes()
                &&& !main_table_view.unwrap().valid_item_indices().contains(item_index)
                &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                &&& u64::bytes_parseable(crc_bytes)
                &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                &&& K::bytes_parseable(key_bytes)
                &&& 0 <= metadata.item_index < overall_metadata.num_keys
                &&& key == entry.key
                &&& metadata == entry.entry
                &&& new_mem is Some
                &&& new_main_table_view == Some(main_table_view.unwrap().update(main_table_index as int, entry@))
                &&& entry@ == MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }
                &&& new_main_table_view.unwrap().valid_item_indices() ==
                    main_table_view.unwrap().valid_item_indices().insert(entry.entry.item_index)
            }),
            self.inv_mem(self.powerpm@.durable_state),
            old_self.tentative_view().unwrap().create(main_table_index as int, key, item) is Ok,
            self.tentative_view() ==
                Some(old_self.tentative_view().unwrap().create(main_table_index as int, key, item).unwrap()),
            self.tentative_main_table() ==
                old_self.tentative_main_table().update(
                    main_table_index as int,
                    MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }
                ),
            self.tentative_main_table() == self.main_table.tentative_view(),
            self.tentative_item_table() == self.item_table.tentative_view(),
            self.main_table.tentative_view().valid_item_indices() == self.item_table.tentative_valid_indices(),
            PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list,
        ensures
            self.inv(),
        {
            old_self.powerpm.lemma_inv_implies_view_valid();
            pre_append_self.powerpm.lemma_inv_implies_view_valid();
            self.powerpm.lemma_inv_implies_view_valid();
            
            let overall_metadata = self.overall_metadata;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let log_area_addr = overall_metadata.log_area_addr;
            let log_area_size = overall_metadata.log_area_size;

            lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                pre_append_self.powerpm@,
                self.powerpm@,
                self.version_metadata,
                self.overall_metadata
            );

            assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).durable_state =~=
                   get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).durable_state);
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).read_state =~=
                   get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat).read_state);

            assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat).durable_state =~=
                   get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat).durable_state);
            assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat).read_state =~=
                   get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                      self.overall_metadata.item_table_size as nat).read_state);
        }

        proof fn lemma_finalize_tentative_create(
            self,
            old_self: Self,
            pre_append_self: Self,
            key: K,
            item: I,
            main_table_index: u64,
            item_index: u64,
            log_entry: PhysicalOpLogEntry,
        )
        requires
            old_self.valid(),
            // old_self.pending_alloc_inv(),
            old_self.tentative_item_table_valid(),
            pre_append_self.inv(),
            ({
                let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
                let new_valid_item_indices = old_valid_item_indices.insert(item_index);
                &&& pre_append_self.tentative_hypothetical_item_table_valid(new_valid_item_indices)
                &&& pre_append_self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                    old_self.tentative_item_table().update(item_index as int, item)
            }),
            self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
            log_entry@.inv(self.version_metadata, self.overall_metadata),
            self.log@ == pre_append_self.log@.tentatively_append_log_entry(log_entry@),
            log_entry_does_not_modify_free_main_table_entries(log_entry@, self.main_table.free_indices(),
                                                              self.overall_metadata),
            self.powerpm.inv(),
            pre_append_self.powerpm@.len() == self.powerpm@.len() == self.overall_metadata.region_size,
            pre_append_self.tentative_main_table() == old_self.tentative_main_table(),
            views_differ_only_in_log_region(pre_append_self.powerpm@, self.powerpm@,
                                            self.overall_metadata.log_area_addr as nat,
                                            self.overall_metadata.log_area_size as nat),
            log_entry_does_not_modify_addresses(log_entry@, self.overall_metadata.item_table_addr as nat,
                                                self.overall_metadata.item_table_size as nat),
            log_entry.absolute_addr + log_entry.len <= self.powerpm@.len(),
            pre_append_self.version_metadata == old_self.version_metadata,
            pre_append_self.overall_metadata == old_self.overall_metadata,
            self.version_metadata == old_self.version_metadata,
            self.overall_metadata == old_self.overall_metadata,
            main_table_index < self.overall_metadata.num_keys,
            pre_append_self.main_table.tentative_view().durable_main_table[main_table_index as int] ==
                Some(MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            pre_append_self.main_table.tentative_view().durable_main_table[main_table_index as int] == 
                Some(MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            log_entries_do_not_modify_item_table(pre_append_self.log@.physical_op_list,
                                                 pre_append_self.overall_metadata),

            !pre_append_self.log@.op_list_committed,
            pre_append_self.main_table.tentative_view() ==
                old_self.main_table.tentative_view().update(
                    main_table_index as int,
                    MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }),
            pre_append_self.item_table.tentative_view() ==
                old_self.item_table.tentative_view().update(item_index as int, item),

            pre_append_self.main_table.tentative_view().valid_item_indices() ==
                old_self.main_table.tentative_view().valid_item_indices().insert(item_index),
            pre_append_self.item_table.tentative_valid_indices() ==
                old_self.item_table.tentative_valid_indices().insert(item_index),
            !self.log@.op_list_committed,
            self.pending_updates@ == pre_append_self.pending_updates@.push(log_entry),
            self == (Self{ powerpm: self.powerpm, log: self.log, pending_updates: self.pending_updates, ..pre_append_self }),
            ({
                let mem = pre_append_self.powerpm@.read_state;
                let op_log = pre_append_self.log@.physical_op_list;
                let overall_metadata = self.overall_metadata;
                let current_tentative_state = apply_physical_log_entries(mem, op_log).unwrap();
                let main_table_region = extract_bytes(current_tentative_state, 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let main_table_view = parse_main_table::<K>(main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                let new_mem = apply_physical_log_entry(current_tentative_state, log_entry@);
                let new_main_table_region = extract_bytes(new_mem.unwrap(), 
                    overall_metadata.main_table_addr as nat, overall_metadata.main_table_size as nat);
                let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                    overall_metadata.num_keys, overall_metadata.main_table_entry_size);
                let entry_bytes = extract_bytes(
                    main_table_region,
                    index_to_offset(main_table_index as nat, overall_metadata.main_table_entry_size as nat),
                    overall_metadata.main_table_entry_size as nat
                );
                let crc_bytes = extract_bytes(entry_bytes, u64::spec_size_of(), u64::spec_size_of());
                let metadata_bytes = extract_bytes(entry_bytes, u64::spec_size_of() * 2,
                                                   ListEntryMetadata::spec_size_of());
                let key_bytes = extract_bytes(
                    entry_bytes, u64::spec_size_of() * 2 + ListEntryMetadata::spec_size_of(), K::spec_size_of()
                );
                let crc = u64::spec_from_bytes(crc_bytes);
                let metadata = ListEntryMetadata::spec_from_bytes(metadata_bytes);
                let key = K::spec_from_bytes(key_bytes);
                let entry = pre_append_self.main_table.outstanding_entries@[main_table_index];
                let item_index = entry.entry.item_index;
                &&& apply_physical_log_entries(mem, op_log) is Some
                &&& pre_append_self.main_table.outstanding_entries[main_table_index] is Some
                &&& main_table_view is Some
                &&& forall|i| 0 <= i < overall_metadata.num_keys &&
                       #[trigger] main_table_view.unwrap().durable_main_table[i] is Some
                       ==> main_table_view.unwrap().durable_main_table[i].unwrap().key != entry.key
                &&& metadata_bytes == entry.entry.spec_to_bytes()
                &&& key_bytes == entry.key.spec_to_bytes()
                &&& !main_table_view.unwrap().valid_item_indices().contains(item_index)
                &&& crc == spec_crc_u64(metadata_bytes + key_bytes)
                &&& u64::bytes_parseable(crc_bytes)
                &&& ListEntryMetadata::bytes_parseable(metadata_bytes)
                &&& K::bytes_parseable(key_bytes)
                &&& 0 <= metadata.item_index < overall_metadata.num_keys
                &&& key == entry.key
                &&& metadata == entry.entry
                &&& new_mem is Some
                &&& new_main_table_view == Some(main_table_view.unwrap().update(main_table_index as int, entry@))
                &&& entry@ == MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }
                &&& new_main_table_view.unwrap().valid_item_indices() ==
                    main_table_view.unwrap().valid_item_indices().insert(entry.entry.item_index)
            }),
            PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list,
        ensures
            self.inv(),
            old_self.tentative_view().unwrap().create(main_table_index as int, key, item) is Ok,
            self.tentative_view() ==
                Some(old_self.tentative_view().unwrap().create(main_table_index as int, key, item).unwrap()),
            self.tentative_main_table() ==
                old_self.tentative_main_table().update(
                    main_table_index as int,
                    MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) }
                ),
            self.tentative_main_table() == self.main_table.tentative_view(),
            self.tentative_item_table() == self.item_table.tentative_view(),
            self.main_table.tentative_view().valid_item_indices() == self.item_table.tentative_valid_indices(),
        {
            old_self.powerpm.lemma_inv_implies_view_valid();
            pre_append_self.powerpm.lemma_inv_implies_view_valid();
            self.powerpm.lemma_inv_implies_view_valid();
            
            let overall_metadata = self.overall_metadata;
            let main_table_addr = overall_metadata.main_table_addr;
            let main_table_size = overall_metadata.main_table_size;
            let item_table_addr = overall_metadata.item_table_addr;
            let item_table_size = overall_metadata.item_table_size;
            let log_area_addr = overall_metadata.log_area_addr;
            let log_area_size = overall_metadata.log_area_size;
            
            assert(self.inv_mem(self.powerpm@.durable_state)) by {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    pre_append_self.powerpm@,
                    self.powerpm@,
                    self.version_metadata,
                    self.overall_metadata
                );
                let s = self.powerpm@.durable_state;
                let pre_s = pre_append_self.powerpm@.durable_state;
                let recovered_log = UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata);
                assert(recovered_log == Some(AbstractOpLogState::initialize())) by {
                    self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                }
                let pre_recovered_log = UntrustedOpLog::<K, L>::recover(pre_s, self.version_metadata,
                                                                        self.overall_metadata);
                assert(pre_recovered_log == Some(AbstractOpLogState::initialize())) by {
                    pre_append_self.log.lemma_reveal_opaque_op_log_inv(pre_append_self.powerpm,
                                                                       pre_append_self.version_metadata,
                                                                       pre_append_self.overall_metadata);
                }
                assert(apply_physical_log_entries(s, recovered_log.unwrap().physical_op_list) == Some(s));
                assert(apply_physical_log_entries(pre_s, pre_recovered_log.unwrap().physical_op_list) == Some(pre_s));
                assert(extract_bytes(s, main_table_addr as nat, main_table_size as nat) =~=
                       extract_bytes(pre_s, main_table_addr as nat, main_table_size as nat));
                assert(extract_bytes(s, item_table_addr as nat, item_table_size as nat) =~=
                       extract_bytes(pre_s, item_table_addr as nat, item_table_size as nat));
                assert(Self::physical_recover(s, self.version_metadata, self.overall_metadata) ==
                       Self::physical_recover(pre_s, self.version_metadata, self.overall_metadata));
                assert(Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@));
            }
            
            let tentative_state_before_create_validify_log_entry =
                prove_unwrap(
                    apply_physical_log_entries(
                        pre_append_self.powerpm@.read_state,
                        pre_append_self.log@.physical_op_list
                    )
                );
            let tentative_state_after_create_validify_log_entry =
                prove_unwrap(
                    apply_physical_log_entry(tentative_state_before_create_validify_log_entry,
                                             log_entry@)
                );
            assert(
                self.log@.physical_op_list ==
                pre_append_self.log@.physical_op_list.push(log_entry@)
            );
            let current_tentative_state =
                apply_physical_log_entries(
                    self.powerpm@.read_state,
                    self.log@.physical_op_list
                );
            assert(current_tentative_state is Some &&
                   extract_bytes(current_tentative_state.unwrap(), self.overall_metadata.main_table_addr as nat,
                                 self.overall_metadata.main_table_size as nat) ==
                   extract_bytes(tentative_state_after_create_validify_log_entry,
                                 self.overall_metadata.main_table_addr as nat,
                                 self.overall_metadata.main_table_size as nat)) by {
                lemma_apply_log_entries_then_apply_log_entry_equivalent_to_push_then_apply(
                    pre_append_self.powerpm@.read_state,
                    pre_append_self.log@.physical_op_list,
                    log_entry@,
                );
                assert(tentative_state_after_create_validify_log_entry ==
                       apply_physical_log_entries(
                           pre_append_self.powerpm@.read_state,
                           self.log@.physical_op_list
                       ).unwrap());
                lemma_effect_of_apply_physical_log_entries_on_views_differing_only_in_log_region(
                    pre_append_self.powerpm@,
                    self.powerpm@,
                    self.log@.physical_op_list,
                    self.version_metadata,
                    self.overall_metadata
                );
                assert(apply_physical_log_entries(pre_append_self.powerpm@.read_state,
                                                  self.log@.physical_op_list) is Some);
                assert(apply_physical_log_entries(self.powerpm@.read_state,
                                                  self.log@.physical_op_list) is Some);
                let mem1_plus = apply_physical_log_entries(pre_append_self.powerpm@.read_state,
                                                           self.log@.physical_op_list).unwrap();
                let mem2_plus = apply_physical_log_entries(self.powerpm@.read_state,
                                                           self.log@.physical_op_list).unwrap();
                assert(extract_bytes(mem1_plus, self.overall_metadata.main_table_addr as nat,
                                     self.overall_metadata.main_table_size as nat) ==
                       extract_bytes(mem2_plus, self.overall_metadata.main_table_addr as nat,
                                     self.overall_metadata.main_table_size as nat));
            }
            let current_tentative_state = prove_unwrap(current_tentative_state);
            let entry = MainTableViewEntry::<K>{ key, entry: ListEntryMetadata::spec_new(0, 0, 0, 0, item_index) };
            assert(old_self.tentative_main_table_valid());
            assert(self.tentative_main_table_valid());
            let entry = pre_append_self.main_table.outstanding_entries@[main_table_index];
            assert(self.tentative_main_table() ==
                   pre_append_self.tentative_main_table().update(main_table_index as int, entry@));
            assert(self.tentative_main_table() ==
                   old_self.tentative_main_table().update(main_table_index as int, entry@));
            assert(entry.key == key);
            assert(entry.entry.item_index == item_index);

            let old_valid_item_indices = old_self.tentative_main_table().valid_item_indices();
            let new_valid_item_indices = old_valid_item_indices.insert(item_index);
            let old_tentative_state_bytes =
                apply_physical_log_entries(pre_append_self.powerpm@.read_state,
                                           pre_append_self.log@.physical_op_list).unwrap();
            let old_tentative_item_table_bytes =
                extract_bytes(old_tentative_state_bytes, item_table_addr as nat,
                              item_table_size as nat);
            let new_tentative_state_bytes =
                apply_physical_log_entries(self.powerpm@.read_state, self.log@.physical_op_list).unwrap();
            let new_tentative_item_table_bytes =
                extract_bytes(new_tentative_state_bytes, item_table_addr as nat, item_table_size as nat);

            lemma_log_replay_preserves_size(pre_append_self.powerpm@.read_state,
                                            pre_append_self.log@.physical_op_list);
            assert(log_entries_do_not_modify_item_table(self.log@.physical_op_list, self.overall_metadata)) by {
                assert forall|i: nat| i < self.log@.physical_op_list.len() implies
                    log_entry_does_not_modify_addresses(#[trigger] self.log@.physical_op_list[i as int],
                                                        overall_metadata.item_table_addr as nat,
                                                        overall_metadata.item_table_size as nat) by {
                    if i < pre_append_self.log@.physical_op_list.len() {
                        assert(self.log@.physical_op_list[i as int] ==
                               pre_append_self.log@.physical_op_list[i as int]);
                        assert(log_entry_does_not_modify_addresses(pre_append_self.log@.physical_op_list[i as int],
                                                                   overall_metadata.item_table_addr as nat,
                                                                   overall_metadata.item_table_size as nat));
                    }
                    else {
                        assert(self.log@.physical_op_list[i as int] == log_entry@);
                    }
                }
            }
            lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

            assert(new_tentative_item_table_bytes =~= old_tentative_item_table_bytes) by {
                assert forall|i: int| 0 <= i < new_tentative_item_table_bytes.len() implies
                    new_tentative_item_table_bytes[i] == old_tentative_item_table_bytes[i] by {
                    assert(new_tentative_item_table_bytes[i] ==
                           new_tentative_state_bytes[i + item_table_addr]);
                    assert(old_tentative_item_table_bytes[i] ==
                           old_tentative_state_bytes[i + item_table_addr]);
                    assert(new_tentative_state_bytes[i + item_table_addr] ==
                           self.powerpm@.read_state[i + item_table_addr]) by {
                        self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata,
                                                                self.overall_metadata);
                        lemma_item_table_bytes_unchanged_by_applying_log_entries(
                            self.powerpm@.read_state,
                            self.log@.physical_op_list,
                            self.version_metadata,
                            self.overall_metadata
                        );
                    }
                    assert(old_tentative_state_bytes[i + item_table_addr] ==
                           pre_append_self.powerpm@.read_state[i + item_table_addr]) by {
                        pre_append_self.log.lemma_reveal_opaque_op_log_inv(
                            pre_append_self.powerpm, pre_append_self.version_metadata,
                            pre_append_self.overall_metadata);
                        lemma_item_table_bytes_unchanged_by_applying_log_entries(
                            pre_append_self.powerpm@.read_state,
                            pre_append_self.log@.physical_op_list,
                            pre_append_self.version_metadata,
                            pre_append_self.overall_metadata
                        );
                    }
                    assert(pre_append_self.powerpm@.durable_state[i + item_table_addr] ==
                           self.powerpm@.durable_state[i + item_table_addr]);
                }
            }
            assert(self.tentative_hypothetical_item_table_valid(new_valid_item_indices));
            assert(self.tentative_hypothetical_item_table(new_valid_item_indices) ==
                   pre_append_self.tentative_hypothetical_item_table(new_valid_item_indices));

            assert(pre_append_self.tentative_hypothetical_item_table(self.tentative_main_table().valid_item_indices())
                   == self.tentative_item_table());
            assert(self.tentative_item_table() == pre_append_self.tentative_item_table().update(item_index as int,
                                                                                                item));
            assert(self.tentative_item_table() == old_self.tentative_item_table().update(item_index as int, item));
            assert(self.tentative_view() is Some);
            assert(old_self.tentative_view() is Some);
            assert(self.tentative_main_table() == old_self.tentative_main_table().update(main_table_index as int,
                                                                                         entry@));
            assert(self.tentative_view().unwrap() =~=
                   old_self.tentative_view().unwrap().create(main_table_index as int, key, item).unwrap());
            
            assert(self.main_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                                          self.overall_metadata.main_table_size as nat),
                                       self.overall_metadata)) by {
                assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                          self.overall_metadata.main_table_size as nat) =~=
                       get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                          self.overall_metadata.main_table_size as nat));
            }
            assert(self.item_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                                          self.overall_metadata.item_table_size as nat),
                                       self.overall_metadata)) by {
                assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                          self.overall_metadata.item_table_size as nat) =~=
                       get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                          self.overall_metadata.item_table_size as nat));
            }
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) =~= self.log@.physical_op_list);

            self.lemma_helper_for_finalize_tentative_create(old_self, pre_append_self, key, item, main_table_index,
                                                            item_index, log_entry);
        }

        // Creates a new durable record in the KV store. Note that since the durable KV store 
        // identifies records by their metadata table index, rather than their key, this 
        // function does NOT return an error if you attempt to create two records with the same 
        // key. Returns the metadata index and the location of the list head node.
        // TODO: Should require caller to prove that the key doesn't already exist in order to create it.
        // The caller should do this because this can be done quickly with the volatile info.
        #[verifier::rlimit(10)]
        pub fn tentative_create(
            &mut self,
            key: &K,
            item: &I,
            kvstore_id: u128,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(u64, u64), KvError<K>>)
            requires
                old(self).valid(),
                !old(self).transaction_committed(),
                old(self).tentative_view() is Some,
                forall|e| #[trigger] old(self).tentative_view().unwrap().contents.contains_value(e) ==> e.key != key,
                forall |s| {
                    &&& Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).powerpm_view().len() >= VersionMetadata::spec_size_of(),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                self@ == old(self)@,
                !self.transaction_committed(),
                self.tentative_view_inv(),
                perm.check_permission(self.powerpm_view().durable_state),
                ({
                    match result {
                        Ok((offset, head_node)) => {
                            &&& old(self).tentative_view().unwrap().create(offset as int, *key, *item) is Ok
                            &&& self.tentative_view() ==
                                Some(old(self).tentative_view().unwrap().create(offset as int, *key, *item).unwrap())
                        },
                        Err(KvError::OutOfSpace) => {
                            &&& self@ == old(self)@
                            &&& Some(self@) == self.tentative_view()
                            &&& self.tentative_view() ==
                                   Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                    self.spec_overall_metadata(),
                                                                    AbstractOpLogState::initialize())
                        },
                        Err(_) => false,
                    }
                })
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
            hide(reverse_item_mapping_exists);

            let ghost num_keys = self.overall_metadata.num_keys;
            let ghost main_table_entry_size = self.overall_metadata.main_table_entry_size;
            let ghost main_table_addr = self.overall_metadata.main_table_addr;
            let ghost main_table_size = self.overall_metadata.main_table_size;

            proof {
                self.lemma_if_key_missing_from_tentative_view_then_missing_from_tentative_main_table(*key);
            }
            
            // 1. find a free slot in the item table and tentatively write the new item there

            let ghost is_writable_item_table_addr = self.get_writable_mask_for_item_table();
            let ghost item_table_subregion_condition = self.condition_preserved_by_subregion_masks();
            proof {
                self.lemma_writable_mask_for_item_table_suitable_for_creating_subregion(perm);
            }
            let item_table_subregion = PoWERPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.powerpm,
                Tracked(perm),
                self.overall_metadata.item_table_addr,
                Ghost(self.overall_metadata.item_table_size as nat),
                Ghost(is_writable_item_table_addr),
                Ghost(item_table_subregion_condition),
            );

            let ghost tentative_state_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            let ghost tentative_main_table_region = extract_bytes(tentative_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size).unwrap();
            let ghost main_table_subregion_view = get_subregion_view(self.powerpm@,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);

            // Establish some facts about the pending allocation invariants. When we tentatively write an item,
            // we'll break the item table's pending alloc invariant, but the metadata table invariant will 
            // be maintained.
            assert(main_table_subregion_view.durable_state == extract_bytes(self.powerpm@.durable_state,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));

            let ghost self_before_tentative_item_write = *self;
            assert(self.item_table.free_list().disjoint(self.item_table.tentative_valid_indices())) by {
                reveal(DurableItemTable::opaquable_inv);
            }
            let item_index = match self.item_table.tentatively_write_item(
                &item_table_subregion,
                &mut self.powerpm,
                &item, 
                Tracked(perm),
                Ghost(self.overall_metadata),
            ) {
                Ok(item_index) => item_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                            *old(self), item_table_subregion, perm
                        );
                    }
                    self.general_abort_after_failed_operation(Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            };

            proof {
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                    *old(self), item_table_subregion, perm
                );
                self.lemma_reestablish_inv_after_tentatively_write_item(*old(self), item_index, *item);
                assert(perm.check_permission(self.powerpm@.durable_state));
            }
            
            assert(self.tentative_item_table() == old(self).tentative_item_table());
            assert(self.inv());

            // 2. Just use a head index of 0 since the list should start empty.
            let head_index = 0;

            // 3. find a free slot in the metadata table and tentatively write a new entry to it
            let ghost is_writable_main_table_addr = self.get_writable_mask_for_main_table();
            let ghost main_table_subregion_condition = self.condition_preserved_by_subregion_masks();
            proof {
                self.lemma_writable_mask_for_main_table_suitable_for_creating_subregion(perm);
            }
            let main_table_subregion = PoWERPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.powerpm,
                Tracked(perm),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat),
                Ghost(is_writable_main_table_addr),
                Ghost(main_table_subregion_condition),
            );

            proof {
                self.lemma_main_table_subregion_grants_access_to_free_slots(main_table_subregion);
            }

            assert(self.tentative_item_table() == old(self).tentative_item_table());

            let ghost self_before_main_table_create = *self;
            let main_table_index = match self.main_table.tentative_create(
                &main_table_subregion,
                &mut self.powerpm,
                head_index, 
                item_index, 
                key,
                Tracked(perm),
                Ghost(self.overall_metadata),
            ) {
                Ok(main_table_index) => main_table_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                            self_before_main_table_create, main_table_subregion, perm
                        );
                    }
                    self.general_abort_after_failed_operation(Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            };

            proof {
                assert(self_before_main_table_create.main_table@.durable_main_table[main_table_index as int] is None)
                by { reveal(MainTable::opaquable_inv); }

                assert(old(self).tentative_main_table().durable_main_table[main_table_index as int] is None) by
                {
                    let durable_state_bytes = old(self).powerpm@.durable_state;
                    let tentative_state_bytes = apply_physical_log_entries(
                        old(self).powerpm@.read_state,
                        old(self).log@.physical_op_list
                    ).unwrap();
                    let durable_main_table_region =
                        extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat);
                    let tentative_main_table_region =
                        extract_bytes(tentative_state_bytes, self.overall_metadata.main_table_addr as nat,
                                      self.overall_metadata.main_table_size as nat);
                    let durable_main_table_view =
                        parse_main_table::<K>(durable_main_table_region, self.overall_metadata.num_keys,
                                              self.overall_metadata.main_table_entry_size).unwrap();
                    let tentative_main_table_view =
                        parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                                              self.overall_metadata.main_table_entry_size).unwrap();
                    assert(tentative_main_table_view.durable_main_table[main_table_index as int] is None) by {
                        reveal(MainTable::opaquable_inv);
                    }
                    assert(old(self).tentative_main_table().durable_main_table[main_table_index as int] is None);
                }
                let t = self_before_main_table_create.tentative_main_table().durable_main_table;
                assert(forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Some ==> t[i].unwrap().key != key);
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                    self_before_main_table_create, main_table_subregion, perm
                );
                self.lemma_justify_validify_log_entry(*old(self), self_before_main_table_create,
                                                      main_table_subregion, main_table_index,
                                                      item_index, head_index, *key, *item, perm);
            }

            assert(self_before_main_table_create.tentative_main_table() == old(self).tentative_main_table());
            assert(self.tentative_main_table() == self_before_main_table_create.tentative_main_table());

            let ghost self_before_create_validify_log_entry = *self;
            let log_entry = self.main_table.create_validify_log_entry(
                Ghost(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                         self.overall_metadata.main_table_size as nat)),
                Ghost(self.powerpm@.read_state),
                main_table_index,
                Ghost(self.version_metadata), &self.overall_metadata,
                Ghost(self.log@.physical_op_list),
            );

            // Create a crash predicate for the validify operation and prove that it ensures the validify
            // will be crash consistent.
            let ghost crash_pred = |s: Seq<u8>| {
                &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
            };
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                self.lemma_condition_preserved_by_subregion_masks_preserved_after_main_table_subregion_updates(
                    self_before_main_table_create, main_table_subregion, perm
                );
            }

            let ghost log_with_new_entry = self.log@.tentatively_append_log_entry(log_entry@);
            let ghost current_flushed_mem = self.powerpm@.read_state;

            let ghost pre_append_self = *self;
            assert(pre_append_self == self_before_create_validify_log_entry);

            proof {
                let new_log = self.log@.tentatively_append_log_entry(log_entry@);
                assert(new_log.physical_op_list == self.log@.physical_op_list.push(log_entry@));
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    new_log.physical_op_list).unwrap();
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, new_log.physical_op_list);

                let old_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();
                lemma_apply_log_entries_then_apply_log_entry_equivalent_to_push_then_apply(self.powerpm@.read_state,
                    self.log@.physical_op_list, log_entry@);
                assert(apply_physical_log_entry(old_tentative_bytes, log_entry@).unwrap() == new_tentative_bytes);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, new_log.physical_op_list);

                let recovered_state = Self::physical_recover_after_applying_log(new_tentative_bytes, self.overall_metadata);
                assert(recovered_state is Some) by {
                    let main_table_region = extract_bytes(new_tentative_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let item_table_region = extract_bytes(new_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                    let list_area_region = extract_bytes(new_tentative_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
                
                    let main_table_view = parse_main_table::<K>(
                        main_table_region, 
                        self.overall_metadata.num_keys,
                        self.overall_metadata.main_table_entry_size
                    );
                    assert(main_table_view is Some);

                    lemma_establish_extract_bytes_equivalence(new_tentative_bytes, self.powerpm@.read_state);
                    lemma_establish_extract_bytes_equivalence(new_tentative_bytes, old_tentative_bytes);

                    lemma_item_table_bytes_unchanged_by_applying_log_entries(new_tentative_bytes,
                        new_log.physical_op_list, self.version_metadata, self.overall_metadata);

                    assert(item_table_region == 
                        extract_bytes(old_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));

                    let item_table_view = parse_item_table::<I, K>(
                        item_table_region,
                        self.overall_metadata.num_keys as nat,
                        main_table_view.unwrap().valid_item_indices()
                    );
                    assert(item_table_view is Some);
                }
            }

            self.append_log_entry_helper(Ghost(pre_append_self), log_entry, Ghost(crash_pred), Tracked(perm))?;

            proof {
                self.powerpm.lemma_inv_implies_view_valid();
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).powerpm@, self.powerpm@, self.version_metadata, self.overall_metadata
                );
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));  
            }

/*
            let result = self.log.tentatively_append_log_entry(&mut self.powerpm, &log_entry, self.version_metadata,
                                                               self.overall_metadata, Ghost(crash_pred), Tracked(perm));
            match result {
                Ok(()) => {}
                Err(e) => {
                    proof {
                        lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                            pre_append_self.powerpm@.durable_state,
                            self.powerpm@.durable_state,
                            self.version_metadata,
                            self.overall_metadata
                        );
                    }
                    let ghost main_table_subregion_view =
                        get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                           self.overall_metadata.main_table_size as nat);
                    assert(main_table_subregion_view.durable_state =~=
                           get_subregion_view(pre_append_self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                              self.overall_metadata.main_table_size as nat).durable_state);
                    assert(parse_main_table::<K>(main_table_subregion_view.durable_state,
                                                 self.overall_metadata.num_keys, 
                                                 self.overall_metadata.main_table_entry_size) is Some) by {
//                        lemma_persistent_memory_view_can_crash_as_flushed(pre_append_self.powerpm@.flush());
//                        assert(pre_append_self.powerpm@.can_crash_as(pre_append_self.powerpm@.read_state));
//                        assert(views_differ_only_in_log_region(pre_append_self.powerpm@.flush(), self.powerpm@,
//                                                               self.overall_metadata.log_area_addr as nat,
//                                                               self.overall_metadata.log_area_size as nat));
                        /*
                        assert(extract_bytes(pre_append_self.powerpm@.read_state,
                                             self.overall_metadata.main_table_addr as nat,
                                             self.overall_metadata.main_table_size as nat) =~=
                               extract_bytes(self.powerpm@.read_state,
                                             self.overall_metadata.main_table_addr as nat,
                                             self.overall_metadata.main_table_size as nat));
                        */
                        assert(main_table_subregion_view.durable_state ==
                               extract_bytes(self.powerpm@.durable_state,
                                             self.overall_metadata.main_table_addr as nat,
                                             self.overall_metadata.main_table_size as nat));
                        assert(main_table_subregion_view.durable_state ==
                               extract_bytes(pre_append_self.powerpm@.read_state,
                                             self.overall_metadata.main_table_addr as nat,
                                             self.overall_metadata.main_table_size as nat));
                    }
                    self.abort_after_failed_op_log_operation(Ghost(*old(self)), Ghost(pre_append_self), Tracked(perm));
                    return Err(e);
                }
            }

            self.append_log_entry_helper(Ghost(pre_append_self), log_entry, Ghost(crash_pred), Tracked(perm))?;

            proof {
                self.powerpm.lemma_inv_implies_view_valid();
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).powerpm@, self.powerpm@, self.version_metadata, self.overall_metadata
                );
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));  
            }
         */

            // 6. Return the index of the metadata entry so it can be used in the volatile index.
            proof {
                self.lemma_finalize_tentative_create(*old(self), pre_append_self, *key, *item, main_table_index,
                                                     item_index, log_entry);
            }

            Ok((main_table_index, head_index))
        }

        proof fn lemma_tentative_view_after_appending_update_item_log_entry_includes_new_log_entry(
            self,
            old_self: Self,
            index: u64,
            old_item_index: u64,
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
                Self::physical_recover(old_self.powerpm@.durable_state, old_self.version_metadata, self.overall_metadata) == Some(old_self@),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(old_self@),
                self.version_metadata == old_self.version_metadata,
                self.overall_metadata == old_self.overall_metadata,
                old_self.tentative_view() is Some,
                self.powerpm@.len() == old_self.powerpm@.len(),
                self.log@.physical_op_list == old_self.log@.physical_op_list.push(log_entry@),
                tentative_view_bytes.len() == self.powerpm@.len(),
                views_differ_only_in_log_region(self.powerpm@, old_self.powerpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                ({
                    let old_flushed_mem = old_self.powerpm@.read_state;
                    let old_op_log = old_self.log@.physical_op_list;
                    let old_mem_with_old_log_installed = apply_physical_log_entries(old_flushed_mem, old_op_log);
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
                    let current_durable_main_table_view = parse_main_table::<K>(current_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                    let new_main_table_region = extract_bytes(new_mem, 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                    
                    &&& self.overall_metadata.main_table_addr <= log_entry.absolute_addr
                    &&& log_entry.absolute_addr + log_entry.len <=
                        self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size
                    &&& log_entry@.inv(self.version_metadata, self.overall_metadata)

                    &&& old_item_index == current_durable_main_table_view.durable_main_table[index as int].unwrap().item_index()

                    // after applying this log entry to the current tentative state,
                    // this entry's metadata index has been updated
                    &&& new_main_table_view is Some
                    &&& new_main_table_view == current_durable_main_table_view.update_item_index(index as int, item_index)
                    &&& new_main_table_view.unwrap().valid_item_indices() == 
                            current_durable_main_table_view.valid_item_indices().insert(item_index).remove(old_item_index)
                }),
                self.item_table.outstanding_items@ == old_self.item_table.outstanding_items@,
                self.item_table.outstanding_items[item_index] == Some(OutstandingItem::Created(item)),
                
                item_index < self.overall_metadata.num_keys,
                old_item_index < self.overall_metadata.num_keys,
            ensures 
                self.tentative_view() is Some,
                old_self.tentative_view().unwrap().len() == self.tentative_view().unwrap().len(),
                self.tentative_view().unwrap() == old_self.tentative_view().unwrap().update_item(index as int, item).unwrap(),
                self.tentative_main_table() == old_self.tentative_main_table().update_item_index(index as int, item_index).unwrap(),
                self.tentative_item_table() == old_self.tentative_item_table().update(item_index as int, item).delete(old_item_index as int),
        {
            broadcast use pmcopy_axioms;

            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
            lemma_valid_entry_index(index as nat, self.overall_metadata.num_keys as nat, self.overall_metadata.main_table_entry_size as nat);

            let old_flushed_mem = old_self.powerpm@.read_state;
            let flushed_mem = self.powerpm@.read_state;
            let old_op_log = old_self.log@.physical_op_list;
            let op_log = self.log@.physical_op_list;
            
            assert(op_log.subrange(0, old_op_log.len() as int) == old_op_log);

            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(flushed_mem, self.version_metadata,
                self.overall_metadata, op_log);
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(flushed_mem, self.version_metadata,
                self.overall_metadata, old_op_log);
            lemma_log_replay_preserves_size(flushed_mem, op_log);
            lemma_log_replay_preserves_size(flushed_mem, old_op_log);

            let mem_with_old_log_applied = apply_physical_log_entries(flushed_mem, old_op_log).unwrap();
            let mem_with_new_log_applied = apply_physical_log_entries(flushed_mem, op_log).unwrap();

            let new_mem = tentative_view_bytes.map(|pos: int, pre_byte: u8|
                if log_entry.absolute_addr <= pos < log_entry.absolute_addr + log_entry.len {
                    log_entry.bytes[pos - log_entry.absolute_addr]
                } else {
                    pre_byte
                }
            );
            lemma_establish_extract_bytes_equivalence(tentative_view_bytes, new_mem);
            Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old_flushed_mem, flushed_mem,
                old_op_log, self.version_metadata, self.overall_metadata);

            // The only part modified by this log entry is the main table.
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

            lemma_item_table_bytes_unchanged_by_applying_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list, self.version_metadata, self.overall_metadata);

            assert(extract_bytes(self.powerpm@.read_state, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) ==
            extract_bytes(new_mem, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));

            let item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            let old_item_table_subregion_view = get_subregion_view(old_self.powerpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
            assert(item_table_subregion_view.read_state == new_item_table_region);
            assert(old_item_table_subregion_view.read_state == old_item_table_region);

            // The current item table has an outstanding item at item_index, and
            // the corresponding outstanding bytes match it.
            assert(self.item_table.outstanding_item_table_entry_matches_pm_view(
                item_table_subregion_view,
                item_index
            ));

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
                    // When idx == item_index, we want to prove that the current outstanding item at item_index is in the new
                    // tentative state. This is the only tricky case; the rest of the items have stayed the same, but we haven't
                    // previously explicitly validated this one.
                    assert(idx == item_index);
                    assert(outstanding_bytes_match(item_table_subregion_view, offset as int, spec_crc_bytes(I::spec_to_bytes(item))));
                    assert(outstanding_bytes_match(item_table_subregion_view, (offset + u64::spec_size_of()) as int, I::spec_to_bytes(item)));
                    lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, offset as int, spec_crc_bytes(I::spec_to_bytes(item)));
                    lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, (offset + u64::spec_size_of()) as int, I::spec_to_bytes(item));
                    lemma_subrange_of_extract_bytes_equal(new_item_table_region, offset, offset, entry_size, u64::spec_size_of());
                    lemma_subrange_of_extract_bytes_equal(new_item_table_region, offset, offset + u64::spec_size_of(), entry_size, I::spec_size_of());
                } // else, trivial
            }

            // // TODO WITH LIST IMPLEMENTATION
            // assert(DurableList::<K, L>::parse_all_lists(
            //     new_mem_main_table,
            //     new_list_area_region,
            //     self.overall_metadata.list_node_size,
            //     self.overall_metadata.num_list_entries_per_node
            // ) == DurableList::<K, L>::parse_all_lists(
            //     old_tentative_main_table,
            //     old_list_area_region,
            //     self.overall_metadata.list_node_size,
            //     self.overall_metadata.num_list_entries_per_node
            // ));

            assert(old_self.tentative_view().unwrap().contents.dom() == old_self.tentative_view().unwrap().update_item(index as int, item).unwrap().contents.dom());
            assert(self.tentative_view().unwrap().contents == old_self.tentative_view().unwrap().update_item(index as int, item).unwrap().contents);

            assert(self.tentative_item_table() == old_self.tentative_item_table().update(item_index as int, item).delete(old_item_index as int));
        }

        proof fn lemma_item_table_unchanged_by_log_replay(
            self,
            old_self: Self,
            old_tentative_view: Seq<u8>,
            new_tentative_view: Seq<u8>,
        )
            requires 
                self.inv(),
                old_self.inv(),
                new_tentative_view == apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap(),
                old_tentative_view == apply_physical_log_entries(old_self.powerpm@.read_state,
                    old_self.log@.physical_op_list).unwrap(),
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.powerpm@.len() == old_self.powerpm@.len(),
                self.version_metadata == old_self.version_metadata,
                self.overall_metadata == old_self.overall_metadata,
                new_tentative_view.len() == self.powerpm@.len(),
                old_tentative_view.len() == old_self.powerpm@.len(),
                AbstractPhysicalOpLogEntry::log_inv(old_self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
            ensures 
                extract_bytes(new_tentative_view, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) ==
                    extract_bytes(self.powerpm@.read_state, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat),
                extract_bytes(old_tentative_view, old_self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat) ==
                    extract_bytes(old_self.powerpm@.read_state, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat),
        {
            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
            lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(old_self.powerpm@.read_state,
                self.version_metadata, self.overall_metadata, old_self.log@.physical_op_list);
            lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

            // Replaying the log does not change the item table bytes. This depends on a KV store invariant
            lemma_item_table_bytes_unchanged_by_applying_log_entries(old_self.powerpm@.read_state,
                old_self.log@.physical_op_list, self.version_metadata, self.overall_metadata);
            lemma_item_table_bytes_unchanged_by_applying_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list, self.version_metadata, self.overall_metadata);
        
            assert(forall |addr: int| {
                &&& 0 <= addr < self.powerpm@.len()
                &&& self.overall_metadata.item_table_addr <= addr < self.overall_metadata.item_table_addr + self.overall_metadata.item_table_size
            } ==> #[trigger] new_tentative_view[addr] == self.powerpm@.read_state[addr]);
            assert(forall |addr: int| {
                &&& 0 <= addr < self.powerpm@.len()
                &&& self.overall_metadata.item_table_addr <= addr < self.overall_metadata.item_table_addr + self.overall_metadata.item_table_size
            } ==> #[trigger] old_tentative_view[addr] == old_self.powerpm@.read_state[addr]);
            
            lemma_establish_extract_bytes_equivalence(new_tentative_view, self.powerpm@.read_state);
            lemma_establish_extract_bytes_equivalence(old_tentative_view, old_self.powerpm@.read_state);
        }

        proof fn lemma_tentative_item_table_update_does_not_modify_other_regions(
            self,
            old_self: Self,
            old_tentative_view: Seq<u8>,
            new_tentative_view: Seq<u8>,
        )
            requires 
                self.inv(),
                old_self.inv(),
                new_tentative_view == apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap(),
                old_tentative_view == apply_physical_log_entries(old_self.powerpm@.read_state,
                    old_self.log@.physical_op_list).unwrap(),
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.powerpm@.len() == old_self.powerpm@.len(),
                self.version_metadata == old_self.version_metadata,
                self.overall_metadata == old_self.overall_metadata,
                new_tentative_view.len() == self.powerpm@.len(),
                old_tentative_view.len() == old_self.powerpm@.len(),
                self.log@ == old_self.log@,
                AbstractPhysicalOpLogEntry::log_inv(old_self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                forall |addr: int| {
                    ||| self.overall_metadata.main_table_addr <= addr < self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size 
                    ||| self.overall_metadata.log_area_addr <= addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size
                    ||| self.overall_metadata.list_area_addr <= addr < self.overall_metadata.list_area_addr + self.overall_metadata.list_area_size 
                } ==> new_tentative_view[addr] == old_tentative_view[addr],
            ensures
                extract_bytes(new_tentative_view, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat) == 
                    extract_bytes(old_tentative_view, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat),
                extract_bytes(new_tentative_view, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat) == 
                    extract_bytes(old_tentative_view, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                extract_bytes(new_tentative_view, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat) == 
                    extract_bytes(old_tentative_view, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat),
        {
            assert(extract_bytes(new_tentative_view, self.overall_metadata.main_table_addr as nat, 
                self.overall_metadata.main_table_size as nat) == extract_bytes(old_tentative_view,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            assert(extract_bytes(new_tentative_view, self.overall_metadata.log_area_addr as nat, 
                self.overall_metadata.log_area_size as nat) == extract_bytes(old_tentative_view, 
                self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
            assert(extract_bytes(new_tentative_view, self.overall_metadata.list_area_addr as nat, 
                self.overall_metadata.list_area_size as nat) == extract_bytes(old_tentative_view, 
                self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat));   
        }  

        exec fn create_delete_log_entry_helper(
            &self,
            index: u64,
            Ghost(current_tentative_bytes): Ghost<Seq<u8>>,
            Tracked(perm): Tracked<&Perm>,
        ) -> (log_entry: PhysicalOpLogEntry)
            requires 
                self.inv(),
                self.tentative_view_inv(),
                !self.transaction_committed(),
                self.tentative_view() is Some,
                self.main_table.tentative_view().durable_main_table[index as int] is Some,
                0 <= index < self.overall_metadata.num_keys,
                Some(current_tentative_bytes) == apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list),
                current_tentative_bytes.len() == self.overall_metadata.region_size,
                !self.main_table.free_indices().contains(index),
            ensures 
                ({
                    let new_log = self.log@.tentatively_append_log_entry(log_entry@);
                    let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                        new_log.physical_op_list);
                    let new_main_table_region = extract_bytes(new_tentative_bytes.unwrap(), 
                        self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                    let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);

                    // log entry address and length are valid
                    &&& self.overall_metadata.main_table_addr <= log_entry.absolute_addr
                    &&& log_entry.absolute_addr + log_entry.len <=
                            self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size
                    &&& log_entry@.inv(self.version_metadata, self.overall_metadata)

                    &&& new_main_table_view == self.main_table.tentative_view().delete(index as int)
                    &&& Self::physical_recover_after_applying_log(new_tentative_bytes.unwrap(), self.overall_metadata) is Some
                    &&& log_entries_do_not_modify_free_main_table_entries(new_log.physical_op_list,
                                                                        self.main_table.free_indices(),
                                                                        self.overall_metadata)
                })
                
        {
            let pm = self.powerpm.get_pm_region_ref();

            let main_table_subregion = PersistentMemorySubregion::new(
                self.powerpm.get_pm_region_ref(),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                let durable_main_table_bytes = extract_bytes(self.powerpm@.durable_state,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion.view(pm).durable_state == durable_main_table_bytes);
//                assert(main_table_subregion.view(pm).can_crash_as(durable_main_table_bytes));
            }

            let log_entry = self.main_table.create_delete_log_entry(
                Ghost(main_table_subregion.view(pm)),
                Ghost(self.powerpm@),
                index,
                Ghost(self.version_metadata),
                &self.overall_metadata,
                Ghost(current_tentative_bytes), 
            );

            proof {
                // These assertions and lemmas help prove that the tentative view after appending the new entry 
                // reflects the delete operation
                let new_log = self.log@.tentatively_append_log_entry(log_entry@);
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                assert(new_log.physical_op_list == self.log@.physical_op_list.push(log_entry@));
                assert(new_log.physical_op_list.subrange(0, (new_log.physical_op_list.len() - 1) as int) == self.log@.physical_op_list);
                assert(AbstractPhysicalOpLogEntry::log_inv(new_log.physical_op_list, self.version_metadata, self.overall_metadata));
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, new_log.physical_op_list);

                let old_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    new_log.physical_op_list).unwrap();
            
                assert(Self::physical_recover_after_applying_log(old_tentative_bytes, self.overall_metadata) is Some);

                let new_item_table_region = extract_bytes(new_tentative_bytes,
                                                          self.overall_metadata.item_table_addr as nat,
                                                          self.overall_metadata.item_table_size as nat);
                let new_list_area_region = extract_bytes(new_tentative_bytes,
                                                         self.overall_metadata.list_area_addr as nat,
                                                         self.overall_metadata.list_area_size as nat);
                let old_item_table_region = extract_bytes(old_tentative_bytes,
                                                          self.overall_metadata.item_table_addr as nat,
                                                          self.overall_metadata.item_table_size as nat);
                let old_list_area_region = extract_bytes(old_tentative_bytes,
                                                         self.overall_metadata.list_area_addr as nat,
                                                         self.overall_metadata.list_area_size as nat);
            
                assert(new_item_table_region == old_item_table_region);
                assert(new_list_area_region == old_list_area_region);
            }

            return log_entry;
        }

        exec fn append_log_entry_helper(
            &mut self,
            Ghost(pre_self): Ghost<Self>,
            log_entry: PhysicalOpLogEntry,
            Ghost(crash_pred): Ghost<spec_fn(Seq<u8>) -> bool>,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(), KvError<K>>)
            requires 
                old(self).inv(),
                pre_self.inv(),
                !old(self).transaction_committed(),
                !pre_self.transaction_committed(),
                old(self).powerpm@.len() == pre_self.powerpm@.len(),
                old(self).main_table@ == pre_self.main_table@,
                old(self).item_table@ == pre_self.item_table@,
                old(self).durable_list@ == pre_self.durable_list@,
                old(self).log@ == pre_self.log@,
                log_entry.inv(old(self).version_metadata, old(self).overall_metadata),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                Self::physical_recover(old(self).powerpm@.durable_state, old(self).version_metadata, old(self).overall_metadata) == Some(old(self)@),
                forall |s: Seq<u8>| {
                    &&& #[trigger] Self::physical_recover(s, old(self).version_metadata, old(self).overall_metadata) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm@.durable_state)
                } <==> crash_pred(s),
                crash_pred(old(self).powerpm@.durable_state),
                old(self).version_metadata == pre_self.version_metadata,
                old(self).overall_metadata == pre_self.overall_metadata,
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                ({
                    let new_log = old(self).log@.tentatively_append_log_entry(log_entry@);
                    let new_tentative_bytes = apply_physical_log_entries(old(self).powerpm@.read_state,
                        new_log.physical_op_list);
                    &&& new_tentative_bytes matches Some(new_tentative_bytes)
                    &&& Self::physical_recover_after_applying_log(new_tentative_bytes, old(self).overall_metadata) is Some
                }),
                old(self).item_table.durable_valid_indices() == old(self).main_table@.valid_item_indices(),
                crash_pred(old(self).powerpm@.durable_state),
            ensures 
                self.powerpm.inv(),
                self.powerpm_view().len() == old(self).powerpm_view().len(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                self.spec_version_metadata() == old(self).spec_version_metadata(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                no_outstanding_writes_to_version_metadata(self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(self.powerpm_view(), self.spec_overall_metadata_addr() as int),
                self.version_metadata == deserialize_version_metadata(self.powerpm_view().durable_state),
                self.tentative_view() is Some,
                self.main_table@ == old(self).main_table@,
                self.item_table@ == old(self).item_table@,
                self.inv_mem(self.powerpm@.durable_state),
                self.item_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat),self.overall_metadata),
                self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
                perm.check_permission(self.powerpm@.durable_state),
                match result {
                    Ok(()) => {
                        &&& self.log@ == old(self).log@.tentatively_append_log_entry(log_entry@)
                        &&& PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list
                        &&& self.pending_updates@ == old(self).pending_updates@.push(log_entry)
                        &&& views_differ_only_in_log_region(old(self).powerpm@, self.powerpm@, 
                                self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                        &&& self.main_table == old(self).main_table
                        &&& self.item_table == old(self).item_table
                        &&& self.durable_list == old(self).durable_list
                    }
                    Err(KvError::OutOfSpace) => {
                        &&& self.valid()
                        &&& self@ == old(self)@
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                        &&& self.powerpm_view().flush_predicted()
                        &&& self.tentative_view() == Some(self@)
                    }
                    Err(_) => false,
                }
        {
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                self.lemma_tentative_log_entry_append_is_crash_safe(crash_pred, perm);
                self.powerpm.lemma_inv_implies_view_valid();
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));        
            }

            let result = self.log.tentatively_append_log_entry(&mut self.powerpm, &log_entry, self.version_metadata,
                                                               self.overall_metadata, Ghost(crash_pred), Tracked(perm));
            assert(self.powerpm@.valid()) by {
                self.powerpm.lemma_inv_implies_view_valid();
            }
            match result {
                Ok(()) => {}
                Err(e) => {
                    proof {
                        let main_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                            self.overall_metadata.main_table_size as nat);
                        let old_main_table_subregion_view = get_subregion_view(old(self).powerpm@, self.overall_metadata.main_table_addr as nat,
                            self.overall_metadata.main_table_size as nat);
//                        assert(old_main_table_subregion_view.can_crash_as(main_table_subregion_view.durable_state));
                        assert(old_main_table_subregion_view.durable_state =~= main_table_subregion_view.durable_state);
                        assert(parse_main_table::<K>(main_table_subregion_view.durable_state, self.overall_metadata.num_keys, 
                            self.overall_metadata.main_table_entry_size) is Some);
                    }
                    self.abort_after_failed_op_log_operation(Ghost(pre_self), Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            }

            self.pending_updates.push(log_entry);
            assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);

            proof {
                let new_log = old(self).log@.tentatively_append_log_entry(log_entry@).commit_op_log();
                assert(new_log == self.log@.commit_op_log());
                
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, new_log.physical_op_list);
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    new_log.physical_op_list).unwrap();

                assert(Self::physical_recover_after_applying_log(new_tentative_bytes, self.overall_metadata) is Some) by {
                    let old_tentative_bytes = apply_physical_log_entries(old(self).powerpm@.read_state,
                        new_log.physical_op_list).unwrap();
                    lemma_log_replay_preserves_size(old(self).powerpm@.read_state, new_log.physical_op_list);
                    lemma_log_replay_preserves_size(self.powerpm@.read_state, new_log.physical_op_list);
                    Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old(self).powerpm@.read_state,
                        self.powerpm@.read_state, new_log.physical_op_list, self.version_metadata, self.overall_metadata);
                    lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(old_tentative_bytes,
                        new_tentative_bytes, self.version_metadata, self.overall_metadata);
                }

                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(old(self).powerpm@.durable_state,
                    self.powerpm@.durable_state, self.version_metadata, self.overall_metadata);
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(old(self).powerpm@, self.powerpm@,
                    self.version_metadata, self.overall_metadata);

                assert(Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self@))
                by {
                    self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                    let s = self.powerpm@.durable_state;
                    /*
                    let witness = s.map(|i, v| {
                        if self.overall_metadata.log_area_addr <= i < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size {
                            old(self).powerpm@.state[i].flush_byte()
                        } else {
                            v // outside of the log
                        }
                    });
                    */
                    let witness = s;

                    let log_start_addr = self.overall_metadata.log_area_addr;
                    let log_size = self.overall_metadata.log_area_size;

                    assert(states_differ_only_in_log_region(s, witness,
                        self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));

                    lemma_if_views_differ_only_in_region_then_states_do(old(self).powerpm@, self.powerpm@,
                                                                        self.overall_metadata.log_area_addr as nat,
                                                                        self.overall_metadata.log_area_size as nat);
                }

                assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat) == get_subregion_view(old(self).powerpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat));
            }
            Ok(())
        }

        exec fn tentatively_write_item_helper(
            &mut self,
            item_table_subregion: &PoWERPersistentMemorySubregion,
            item: &I,
            Tracked(perm): Tracked<&Perm>
        ) -> (result: Result<u64, KvError<K>>)
            requires 
                item_table_subregion.inv(&old(self).powerpm, perm),
                old(self).item_table.inv(item_table_subregion.view(&old(self).powerpm), old(self).overall_metadata),
                old(self).valid(),
                item_table_subregion.constants() == old(self).powerpm.constants(),
                item_table_subregion.start() == old(self).overall_metadata.item_table_addr,
                item_table_subregion.len() == old(self).overall_metadata.item_table_size,
                item_table_subregion.initial_region_view() == old(self).powerpm@,
                item_table_subregion.is_writable_absolute_addr_fn() == old(self).get_writable_mask_for_item_table(),
                !old(self).transaction_committed(),
                item_table_subregion.len() >= old(self).overall_metadata.item_table_size,
                forall |s| {
                    &&& Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).powerpm_view().len() >= VersionMetadata::spec_size_of(),
                condition_sufficient_to_create_powerpm_subregion(
                    old(self).powerpm@, perm, old(self).overall_metadata.item_table_addr,
                    old(self).overall_metadata.item_table_size as nat,
                    old(self).get_writable_mask_for_item_table(),
                    old(self).condition_preserved_by_subregion_masks(),
                ),
                old(self).tentative_view() is Some,
                item_table_subregion.view(&old(self).powerpm) == item_table_subregion.initial_subregion_view(),
            ensures 
                self.inv(),
                self.powerpm.inv(),
                self.item_table.inv(item_table_subregion.view(&self.powerpm), self.overall_metadata),
                self.overall_metadata == old(self).overall_metadata,
                self.version_metadata == old(self).version_metadata,
                self.powerpm_view().len() == old(self).powerpm_view().len(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                self.spec_version_metadata() == old(self).spec_version_metadata(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                no_outstanding_writes_to_version_metadata(self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(self.powerpm_view(), self.spec_overall_metadata_addr() as int),
                self.item_table@ == old(self).item_table@,
                self.durable_list@ == old(self).durable_list@,
                self.main_table@ == old(self).main_table@,
                self.tentative_view() is Some,
                perm.check_permission(self.powerpm_view().durable_state),
                match result {
                    Ok(index) => {
                        &&& self.main_table == old(self).main_table
                        &&& item_table_subregion.inv(&self.powerpm, perm)
                        &&& views_differ_only_where_subregion_allows(item_table_subregion.initial_region_view(), self.powerpm@,
                                                         self.overall_metadata.item_table_addr as nat,
                                                         self.overall_metadata.item_table_size as nat,
                                                         old(self).get_writable_mask_for_item_table())
                        &&& self.main_table_view_matches(old(self).powerpm@)
                        &&& self.list_area_view_matches(old(self).powerpm@)
                        &&& self.log_area_view_matches(old(self).powerpm@)
                        &&& ({
                                let condition = old(self).condition_preserved_by_subregion_masks();
                                condition(self.powerpm@.durable_state)
                           })
                        &&& index < self.overall_metadata.num_keys
                        &&& self.log@ == old(self).log@
                        &&& forall |i: u64| 0 <= i < self.overall_metadata.num_keys && i != index ==>
                                #[trigger] self.item_table.outstanding_items[i] == old(self).item_table.outstanding_items[i]
                        &&& ({
                                &&& self.item_table.outstanding_items[index] matches Some(outstanding_item)
                                &&& outstanding_item == OutstandingItem::Created(*item)
                            })
                        &&& self.item_table.tentative_view() == old(self).item_table.tentative_view().update(index as int, *item)
                        &&& old(self).item_table.free_list().contains(index)
                        &&& self.tentative_view() == old(self).tentative_view()
                        &&& self.tentative_item_table() == old(self).tentative_item_table()
                        &&& self.tentative_main_table() == old(self).tentative_main_table()
                    }
                    Err(KvError::OutOfSpace) => {
                        &&& self.valid()
                        &&& self@ == old(self)@
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                        &&& self.powerpm_view().flush_predicted()
                        &&& self.tentative_view() == Some(self@)
                    }
                    _ => false
                }
        {
            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            let ghost tentative_main_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size).unwrap();
            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);
            }

            let ghost self_before_tentative_item_write = *self;
            let item_index = match self.item_table.tentatively_write_item(
                item_table_subregion,
                &mut self.powerpm,
                &item, 
                Tracked(perm),
                Ghost(self.overall_metadata),
            ) {
                Ok(item_index) => item_index,
                Err(e) => {
                    proof {
                        self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                            self_before_tentative_item_write, *item_table_subregion, perm);
                        let main_table_subregion_view = get_subregion_view(self.powerpm@,
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);

//                        assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.read_state));
//                        assert(main_table_subregion_view.flush() == get_subregion_view(self.powerpm@.flush(),
//                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                    }
                    self.general_abort_after_failed_operation(Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            };

            proof {
                let current_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();

                self.lemma_condition_preserved_by_subregion_masks_preserved_after_item_table_subregion_updates(
                    *old(self), *item_table_subregion, perm);
                item_table_subregion.lemma_reveal_opaque_inv(&self.powerpm);


                assert(forall |i: u64| 0 <= i < self.overall_metadata.num_keys && i != item_index ==>
                        #[trigger] self.item_table.outstanding_items[i] == old(self).item_table.outstanding_items[i]);
                assert({
                    &&& self.item_table.outstanding_items[item_index] matches Some(outstanding_item)
                    &&& outstanding_item == OutstandingItem::Created(*item)
                });

                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

                // Prove that this operation has not modified the main table, log, or list 
                assert forall |addr: int| {
                    ||| self.overall_metadata.main_table_addr <= addr < self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size 
                    ||| self.overall_metadata.log_area_addr <= addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size
                    ||| self.overall_metadata.list_area_addr <= addr < self.overall_metadata.list_area_addr + self.overall_metadata.list_area_size 
                } implies tentative_view_bytes[addr] == current_tentative_bytes[addr]
                by {
                    lemma_byte_equal_after_recovery_specific_byte(addr, old(self).powerpm@.read_state, 
                        self.powerpm@.read_state, self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                }

                let old_tentative_main_table_bytes = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                let new_tentative_main_table_bytes = extract_bytes(current_tentative_bytes, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
                assert(old_tentative_main_table_bytes == new_tentative_main_table_bytes);

                self.lemma_reestablish_inv_after_tentatively_write_item(*old(self), item_index, *item);
                self.lemma_tentative_item_table_update_does_not_modify_other_regions(*old(self), tentative_view_bytes, current_tentative_bytes);

                // durable MAIN table bytes have not been modified. This follows from the fact that the main table region has 
                // not been modified but is useful to state explicitly so that Verus can automate some reasoning about pending alloc invs
                let old_durable_main_table_bytes = extract_bytes(old(self).powerpm@.durable_state,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let new_durable_main_table_bytes = extract_bytes(self.powerpm@.durable_state,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(new_durable_main_table_bytes == old_durable_main_table_bytes);
                assert(self.main_table.tentative_view() == old(self).main_table.tentative_view());
            
                let new_main_table_region = extract_bytes(current_tentative_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let old_flushed_item_table_region = extract_bytes(old(self).powerpm@.read_state, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let new_flushed_item_table_region = extract_bytes(self.powerpm@.read_state, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                
                let new_main_table_view = parse_main_table::<K>(
                    new_main_table_region, 
                    self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size
                ).unwrap();
                assert(new_main_table_view == self.main_table.tentative_view());

                // Now, prove that the parsed/recovery view of the item table is unchanged 
                // after this write.
                assert(!new_main_table_view.valid_item_indices().contains(item_index));
                lemma_parse_item_table_doesnt_depend_on_fields_of_invalid_entries::<I, K>(
                    old_flushed_item_table_region,
                    new_flushed_item_table_region,
                    self.overall_metadata.num_keys,
                    new_main_table_view.valid_item_indices()
                );
                self.lemma_item_table_unchanged_by_log_replay(*old(self), tentative_view_bytes, current_tentative_bytes);
                assert(self.item_table.tentative_view() =~= old(self).item_table.tentative_view().update(item_index as int, *item));
            }

            Ok(item_index)
        }

        exec fn create_update_item_log_entry_helper(
            &mut self,
            Ghost(pre_self): Ghost<Self>,
            index: u64,
            item_index: u64,
            Ghost(current_tentative_bytes): Ghost<Seq<u8>>,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(PhysicalOpLogEntry, Box<ListEntryMetadata>, Box<K>), KvError<K>>)
            requires 
                old(self).inv(),
                pre_self.inv(),
                pre_self.tentative_view_inv(),
                pre_self.tentative_view().unwrap().contains_key(index as int),
                !old(self).transaction_committed(),
                !pre_self.transaction_committed(),
                old(self).tentative_view() is Some,
                old(self).powerpm@.len() == pre_self.powerpm@.len(),
                old(self).main_table@ == pre_self.main_table@,
                old(self).item_table@ == pre_self.item_table@,
                old(self).durable_list@ == pre_self.durable_list@,
                old(self).log@ == pre_self.log@,
                Some(current_tentative_bytes) == apply_physical_log_entries(old(self).powerpm@.read_state,
                    old(self).log@.physical_op_list),
                old(self).item_table.outstanding_items[item_index] is Some,
                ({
                    let durable_main_table_region = extract_bytes(old(self).powerpm@.durable_state,
                        old(self).overall_metadata.main_table_addr as nat, old(self).overall_metadata.main_table_size as nat);
                    let tentative_main_table_region = extract_bytes(current_tentative_bytes, 
                        old(self).overall_metadata.main_table_addr as nat, old(self).overall_metadata.main_table_size as nat);
                    let tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region,
                        old(self).overall_metadata.num_keys, old(self).overall_metadata.main_table_entry_size);
                    &&& tentative_main_table_view == Some(pre_self.tentative_main_table())
                }),
                forall |i: u64| 0 <= i < old(self).overall_metadata.num_keys ==>
                    old(self).item_table.outstanding_item_table_entry_matches_pm_view(get_subregion_view(old(self).powerpm@, 
                        old(self).overall_metadata.item_table_addr as nat, 
                        old(self).overall_metadata.item_table_size as nat), 
                    i),
                forall |i: u64| 0 <= i < old(self).overall_metadata.num_keys && i != item_index ==>
                    #[trigger] old(self).item_table.outstanding_items[i] == pre_self.item_table.outstanding_items[i],
                old(self).item_table.outstanding_items[item_index] is Some,
                old(self).item_table.outstanding_items[item_index].unwrap() is Created,

                old(self).main_table.tentative_view() == pre_self.main_table.tentative_view(),
                old(self).tentative_main_table().durable_main_table[index as int] is Some,
                old(self).tentative_main_table() == pre_self.tentative_main_table(),
                !old(self).tentative_main_table().valid_item_indices().contains(item_index),
                current_tentative_bytes.len() == old(self).overall_metadata.region_size,
                item_index < old(self).overall_metadata.num_keys,
                old(self).version_metadata == pre_self.version_metadata,
                old(self).overall_metadata == pre_self.overall_metadata,
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                forall |s| {
                    &&& Self::physical_recover(s, old(self).version_metadata, old(self).overall_metadata) ==
                           Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm@.durable_state)
                } ==> #[trigger] perm.check_permission(s),
                perm.check_permission(old(self).powerpm@.durable_state),
            ensures 
                self.inv(),
                self.powerpm_view().len() == old(self).powerpm_view().len(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                self.version_metadata == old(self).version_metadata,
                self.overall_metadata == old(self).overall_metadata,
                old(self).powerpm@.len() == self.powerpm@.len(),
                old(self).main_table@ == self.main_table@,
                old(self).item_table@ == self.item_table@,
                old(self).durable_list@ == self.durable_list@,
                no_outstanding_writes_to_version_metadata(self.powerpm_view()),
                no_outstanding_writes_to_overall_metadata(self.powerpm_view(), self.spec_overall_metadata_addr() as int),
                self.tentative_view() is Some,
                perm.check_permission(self.powerpm@.durable_state),
                match result {
                    Ok((log_entry, old_entry, key)) => {
                        let new_log = self.log@.tentatively_append_log_entry(log_entry@);
                        let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                            new_log.physical_op_list);
                        let new_main_table_region = extract_bytes(new_tentative_bytes.unwrap(), 
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                            self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);

                        let current_main_table_region = extract_bytes(current_tentative_bytes, 
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                        let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                            self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();

                        &&& self.main_table.get_latest_entry(index) is Some
                        &&& old_entry == self.main_table.get_latest_entry(index).unwrap().entry
                        &&& key == self.main_table.get_latest_entry(index).unwrap().key
                        &&& self.main_table.tentative_view().valid_item_indices().contains(old_entry.item_index)

                        // log entry address and length are valid
                        &&& self.overall_metadata.main_table_addr <= log_entry.absolute_addr
                        &&& log_entry.absolute_addr + log_entry.len <=
                                self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size
                        &&& log_entry@.inv(self.version_metadata, self.overall_metadata)

                        // these may be unnecessary
                        &&& new_tentative_bytes is Some
                        &&& new_tentative_bytes == apply_physical_log_entry(current_tentative_bytes, log_entry@)
                        
                        // The whole thing recovers successfully
                        &&& Self::physical_recover_after_applying_log(new_tentative_bytes.unwrap(), self.overall_metadata) is Some

                        // after applying this log entry to the current tentative state,
                        // this entry's metadata index has been updated
                        &&& new_main_table_view is Some
                        &&& new_main_table_view.unwrap() == current_main_table_view.update_item_index(index as int, item_index).unwrap()
                        &&& new_main_table_view.unwrap().valid_item_indices() == 
                                current_main_table_view.valid_item_indices().insert(item_index).remove(old_entry.item_index)

                        // other success case guarantees
                        &&& old(self).log@ == self.log@
                        &&& old(self).powerpm@ == self.powerpm@
                        &&& old(self).main_table == self.main_table
                        &&& old(self).item_table == self.item_table
                        // note -- the actual tentative view doesn't change because we haven't appended to the log yet.
                        // when we do, we'll get the new main table view mentioned above
                        &&& old(self).tentative_view() == self.tentative_view()
                        &&& log_entry_does_not_modify_free_main_table_entries(log_entry@, self.main_table.free_indices(),
                                                                            self.overall_metadata)   
                    }
                    Err(KvError::CRCMismatch) => {
                        &&& self.valid()
                        &&& self@ == old(self)@
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                        &&& !self.constants().impervious_to_corruption()
                        &&& self.powerpm_view().flush_predicted()
                        &&& self.tentative_view() == Some(self@)
                    }
                    Err(_) => false,
                }
        {
            let pm = self.powerpm.get_pm_region_ref();

            let main_table_subregion = PersistentMemorySubregion::new(
                self.powerpm.get_pm_region_ref(),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                let durable_main_table_bytes = extract_bytes(self.powerpm@.durable_state,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion.view(pm).durable_state == durable_main_table_bytes);
            }
            
            let (log_entry, old_entry, key) = match self.main_table.create_update_item_index_log_entry(
                &main_table_subregion,
                pm,
                index,
                item_index,
                &self.overall_metadata,
                Ghost(self.version_metadata),
                Ghost(current_tentative_bytes), 
            ) {
                Ok((log_entry, old_entry, key)) => (log_entry, old_entry, key),
                Err(e) => {
                    proof {
                        let main_table_subregion_view = get_subregion_view(self.powerpm@,
                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
//                        assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.read_state));
//                        assert(main_table_subregion_view.flush() == get_subregion_view(self.powerpm@.flush(),
//                            self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                    }
                    self.general_abort_after_failed_operation(Ghost(pre_self), Tracked(perm));
                    return Err(e);
                }
            };

            assert(old_entry == self.main_table.get_latest_entry(index).unwrap().entry);

            proof {
                // These assertions and lemmas help prove that the tentative view after appending the new entry 
                // reflects the item update
                let new_log = self.log@.tentatively_append_log_entry(log_entry@);
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                assert(new_log.physical_op_list == self.log@.physical_op_list.push(log_entry@));
                assert(new_log.physical_op_list.subrange(0, (new_log.physical_op_list.len() - 1) as int) == self.log@.physical_op_list);
                assert(AbstractPhysicalOpLogEntry::log_inv(new_log.physical_op_list, self.version_metadata, self.overall_metadata));
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, new_log.physical_op_list);

                // We also need to prove that the entire kv store recovers successfully after applying the new log.
                let old_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    new_log.physical_op_list).unwrap();

                let current_main_table_region = extract_bytes(current_tentative_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let current_main_table_view = parse_main_table::<K>(current_main_table_region,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                let old_item_index = current_main_table_view.durable_main_table[index as int].unwrap().item_index();
            
                assert(Self::physical_recover_after_applying_log(old_tentative_bytes, self.overall_metadata) is Some);

                let new_main_table_region = extract_bytes(new_tentative_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let new_item_table_region = extract_bytes(new_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let new_list_area_region = extract_bytes(new_tentative_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
                
                let old_item_table_region = extract_bytes(old_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let old_list_area_region = extract_bytes(old_tentative_bytes, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);
            
                assert(new_item_table_region == old_item_table_region);
                assert(new_list_area_region == old_list_area_region);

                let new_main_table_view = parse_main_table::<K>(
                    new_main_table_region, 
                    self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size
                ).unwrap();
                assert(Some(new_main_table_view) == current_main_table_view.update_item_index(index as int, item_index));


                assert(forall |i: int| 0 <= i < new_main_table_view.durable_main_table.len() && i != index ==> {
                    &&& new_main_table_view.durable_main_table[i] is None ==> current_main_table_view.durable_main_table[i] is None
                    &&& new_main_table_view.durable_main_table[i] matches Some(new_entry) ==> {
                        &&& current_main_table_view.durable_main_table[i] matches Some(current_entry)
                        &&& new_entry == current_entry
                    }
                });

                let entry_size = I::spec_size_of() + u64::spec_size_of();
                assert forall |i: u64| i < self.overall_metadata.num_keys && new_main_table_view.valid_item_indices().contains(i) implies 
                    validate_item_table_entry::<I, K>(#[trigger] extract_bytes(new_item_table_region, index_to_offset(i as nat, entry_size as nat), entry_size))
                by {
                    broadcast use pmcopy_axioms;
                    lemma_valid_entry_index(i as nat, self.overall_metadata.num_keys as nat, entry_size as nat);
                    lemma_entries_dont_overlap_unless_same_index(i as nat, self.overall_metadata.num_keys as nat, entry_size as nat);
                    
                    if i == item_index {
                        let entry_size = I::spec_size_of() + u64::spec_size_of();
                        let start = index_to_offset(i as nat, entry_size as nat) as nat;
                        let item_table_subregion_view = get_subregion_view(self.powerpm@, 
                            self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                        let new_entry_bytes = extract_bytes(new_item_table_region, start, entry_size);
                        let old_entry_bytes = extract_bytes(item_table_subregion_view.read_state, start, entry_size);
                        assert(item_table_subregion_view.len() >= start + u64::spec_size_of() + I::spec_size_of());

                        lemma_item_table_bytes_unchanged_by_applying_log_entries(self.powerpm@.read_state, 
                            new_log.physical_op_list, self.version_metadata, self.overall_metadata);
                        assert(item_table_subregion_view.read_state == extract_bytes(self.powerpm@.read_state, 
                            self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));
                        assert(new_item_table_region == item_table_subregion_view.read_state);
                        
                        assert(self.item_table.outstanding_items@[item_index] is Created);
                        let outstanding_item = self.item_table.outstanding_items@[item_index]->Created_0;
                        assert(self.item_table.outstanding_item_table_entry_matches_pm_view(item_table_subregion_view, i));
                        assert(outstanding_bytes_match(item_table_subregion_view, start as int, spec_crc_bytes(I::spec_to_bytes(outstanding_item))));
                        assert(outstanding_bytes_match(item_table_subregion_view, (start + u64::spec_size_of()) as int, I::spec_to_bytes(outstanding_item)));

                        lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, start as int, spec_crc_bytes(I::spec_to_bytes(outstanding_item)));
                        lemma_outstanding_bytes_match_after_flush(item_table_subregion_view, (start + u64::spec_size_of()) as int, I::spec_to_bytes(outstanding_item));

                        assert(validate_item_table_entry::<I, K>(old_entry_bytes)) by {
                            assert(extract_bytes(old_entry_bytes, 0, u64::spec_size_of()) == spec_crc_bytes(I::spec_to_bytes(outstanding_item)));
                            assert(extract_bytes(old_entry_bytes, u64::spec_size_of(), I::spec_size_of()) == I::spec_to_bytes(outstanding_item));
                        }
                        assert(validate_item_table_entry::<I, K>(new_entry_bytes));
                    } // else, trivial
                }

                assert(validate_item_table_entries::<I, K>(new_item_table_region, self.overall_metadata.num_keys as nat, new_main_table_view.valid_item_indices()));
        
                let new_item_table_view = parse_item_table::<I, K>(
                    new_item_table_region,
                    self.overall_metadata.num_keys as nat,
                    new_main_table_view.valid_item_indices()
                );
                assert(new_item_table_view is Some);
            }
            Ok((log_entry, old_entry, key))
        }

        exec fn update_outstanding_item_index_in_main_table(
            &mut self,
            old_entry: Box<ListEntryMetadata>,
            key: Box<K>,
            index: u64,
            item_index: u64,
        ) 
            requires 
                old(self).inv(),
                !old(self).transaction_committed(),
                old(self).main_table.tentative_view().durable_main_table[index as int] is Some,
                old(self).tentative_item_table() == old(self).item_table.tentative_view(),
                old(self).item_table.durable_valid_indices() == old(self).main_table@.valid_item_indices(),
                old(self).item_table.tentative_valid_indices() == 
                    old(self).main_table.tentative_view().valid_item_indices().remove(old_entry.item_index).insert(item_index),
                old(self).main_table.tentative_view().update_item_index(index as int, item_index) == 
                    Some(old(self).tentative_main_table()),
                old(self).main_table.tentative_view().durable_main_table[index as int] is Some,
                old(self).main_table.tentative_view().durable_main_table[index as int].unwrap().entry == old_entry,
                no_duplicate_item_indexes(old(self).main_table.tentative_view().durable_main_table),
                no_duplicate_item_indexes(old(self).main_table@.durable_main_table),
                !old(self).main_table.tentative_view().valid_item_indices().contains(item_index),
                old(self).main_table.tentative_view().durable_main_table[index as int].unwrap().key == key,
            ensures 
                self.inv(),
                self.tentative_view_inv(),
                self.powerpm@ == old(self).powerpm@,
                self@ == old(self)@,
                !self.transaction_committed(),
                self.constants() == old(self).constants(),
                self.version_metadata == old(self).version_metadata,
                self.overall_metadata == old(self).overall_metadata,
                self.main_table@ == old(self).main_table@,
                self.item_table@ == old(self).item_table@,
                self.log@ == old(self).log@,
        {
            let pm = self.powerpm.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(
                pm,
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            let new_entry = ListEntryMetadata {
                item_index,
                ..*old_entry
            };

            self.main_table.add_tentative_item_update(&main_table_subregion, pm, index, new_entry, key, self.overall_metadata);

            proof {
                assert(self.main_table.tentative_view().valid_item_indices().contains(item_index)) by {
                    let witness = self.main_table.tentative_view().durable_main_table[index as int];
                    assert(witness is Some);
                    assert(witness.unwrap().item_index() == item_index);
                }

                // Prove that all other item indexes in the tentative main table have not been changed
                assert forall |i: u64| {
                    &&& old(self).main_table.tentative_view().valid_item_indices().contains(i) 
                    &&& i != old_entry.item_index 
                    &&& i != item_index 
                } implies self.main_table.tentative_view().valid_item_indices().contains(i) by {
                    // there exists an index in the old main table tentative view with this item index
                    let witness = choose |j: int| {
                        &&& 0 <= j < old(self).main_table.tentative_view().durable_main_table.len() 
                        &&& #[trigger] old(self).main_table.tentative_view().durable_main_table[j] matches Some(entry)
                        &&& entry.item_index() == i
                    };
                    // the value at the witness index has not been modified
                    assert(old(self).main_table.tentative_view().durable_main_table[witness] == 
                        self.main_table.tentative_view().durable_main_table[witness]);
                }

                assert(!self.main_table.tentative_view().valid_item_indices().contains(old_entry.item_index)) by {
                    if self.main_table.tentative_view().valid_item_indices().contains(old_entry.item_index) {
                        let new_main_table_view = self.main_table.tentative_view();
                        let j = choose|j: int| {
                            &&& 0 <= j < new_main_table_view.durable_main_table.len()
                            &&& #[trigger] new_main_table_view.durable_main_table[j] matches Some(entry)
                            &&& entry.item_index() == old_entry.item_index
                        };
                        assert(trigger_main_entry(j));
                        assert(trigger_main_entry(index as int));
                        assert(j != index);
                        assert(false); // proof by contradiction
                    }
                }
                assert(self.main_table.tentative_view().valid_item_indices() == 
                    old(self).main_table.tentative_view().valid_item_indices().remove(old_entry.item_index).insert(item_index));
            }
        }

        pub fn tentative_update_item(
            &mut self,
            offset: u64,
            item: &I,
            kvstore_id: u128,
            Tracked(perm): Tracked<&Perm>,
        ) -> (result: Result<(), KvError<K>>)
            requires 
                old(self).valid(),
                old(self).tentative_view().unwrap().contains_key(offset as int),
                !old(self).transaction_committed(),
                forall |s| {
                    &&& Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).powerpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    &&& tentative_view matches Some(tentative_view)
                    &&& tentative_view.contains_key(offset as int)
                }),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                self@ == old(self)@,
                self.tentative_view_inv(),
                perm.check_permission(self.powerpm_view().durable_state),
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
                                &&& self.spec_num_log_entries_in_current_transaction() == 
                                        old(self).spec_num_log_entries_in_current_transaction() + 1
                            }
                            Err(_) => false
                        }
                    }
                    Err(KvError::OutOfSpace) => {
                        &&& self.valid()
                        &&& Some(self@) == self.tentative_view()
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                    }
                    Err(KvError::CRCMismatch) => {
                        &&& self.valid()
                        &&& Some(self@) == self.tentative_view()
                        &&& self.tentative_view() ==
                                Self::physical_recover_given_log(self.powerpm_view().read_state,
                                                                self.spec_overall_metadata(),
                                                                AbstractOpLogState::initialize())
                        &&& !self.constants().impervious_to_corruption()
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

            let ghost original_tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();

            let item_table_subregion = PoWERPersistentMemorySubregion::new_with_condition::<Perm, PM>(
                &self.powerpm,
                Tracked(perm),
                self.overall_metadata.item_table_addr,
                Ghost(self.overall_metadata.item_table_size as nat),
                Ghost(is_writable_item_table_addr),
                Ghost(item_table_subregion_condition),
            );

            let main_table_subregion = PersistentMemorySubregion::new(
                self.powerpm.get_pm_region_ref(),
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                lemma_log_replay_preserves_size(self.powerpm@.read_state, 
                    self.log@.physical_op_list);
            }

            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            let ghost tentative_main_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
            let ghost tentative_main_table_view = parse_main_table::<K>(tentative_main_table_region, self.overall_metadata.num_keys,
                    self.overall_metadata.main_table_entry_size).unwrap();
            let ghost main_table_subregion_view = get_subregion_view(self.powerpm@,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
//            assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.durable_state));
            assert(main_table_subregion_view.durable_state == extract_bytes(self.powerpm@.durable_state,
                self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));            


            assert(forall|addr: int| {
                &&& 0 <= addr < item_table_subregion.view(&self.powerpm).len()
                &&& address_belongs_to_invalid_item_table_entry::<I>(
                    addr, self.overall_metadata.num_keys,
                    self.item_table.durable_valid_indices().union(self.item_table.tentative_valid_indices())
                )
            } ==> #[trigger] item_table_subregion.is_writable_relative_addr(addr));

            // 2. Tentatively write the new item
            let ghost self_before_tentative_item_write = *self;
            let item_index = self.tentatively_write_item_helper(&item_table_subregion, item, Tracked(perm))?;

            let ghost pre_append_tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            let pm = self.powerpm.get_pm_region_ref();

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

                let main_table_region = extract_bytes(pre_append_tentative_view_bytes, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let durable_main_table_bytes = extract_bytes(self.powerpm@.durable_state,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(main_table_subregion.view(pm).durable_state == durable_main_table_bytes);
                let tentative_main_table = parse_main_table::<K>(main_table_region,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);

                // Prove that if we flush the bytes (and potentially apply the log), this item we just wrote will parse correctly
                assert(item_table_subregion.view(&self.powerpm).read_state == extract_bytes(self.powerpm@.read_state,
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));
                self.lemma_item_table_unchanged_by_log_replay(*old(self), original_tentative_view_bytes, pre_append_tentative_view_bytes);
                assert(extract_bytes(self.powerpm@.read_state, self.overall_metadata.item_table_addr as nat, 
                    self.overall_metadata.item_table_size as nat) == extract_bytes(pre_append_tentative_view_bytes,
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));
            }

            proof {
                // Prove that this operation has not modified the main table, log, or list 
                assert forall |addr: int| {
                    ||| self.overall_metadata.main_table_addr <= addr < self.overall_metadata.main_table_addr + self.overall_metadata.main_table_size 
                    ||| self.overall_metadata.log_area_addr <= addr < self.overall_metadata.log_area_addr + self.overall_metadata.log_area_size
                    ||| self.overall_metadata.list_area_addr <= addr < self.overall_metadata.list_area_addr + self.overall_metadata.list_area_size 
                } implies pre_append_tentative_view_bytes[addr] == tentative_view_bytes[addr]
                by {
                    lemma_byte_equal_after_recovery_specific_byte(addr, old(self).powerpm@.read_state, 
                        self.powerpm@.read_state, self.version_metadata, self.overall_metadata, self.log@.physical_op_list);
                }
                self.lemma_tentative_item_table_update_does_not_modify_other_regions(*old(self), tentative_view_bytes, pre_append_tentative_view_bytes);        

                assert(self.main_table == old(self).main_table);
                assert(self.tentative_main_table() == old(self).tentative_main_table());
                assert(self.main_table.tentative_view() == old(self).main_table.tentative_view());
            }

            // 3. Create a log entry that will overwrite the metadata table entry
            // with a new one containing the new item table index
            let (log_entry, old_entry, key) = self.create_update_item_log_entry_helper(Ghost(*old(self)), offset, item_index,
                Ghost(pre_append_tentative_view_bytes), Tracked(perm))?;

            // 4. Tentatively deallocate the old item index, since it will no longer be valid when
            // this transaction completes
            self.item_table.tentatively_deallocate_item(Ghost(item_table_subregion.view(&self.powerpm)), old_entry.item_index, Ghost(self.overall_metadata));
            assert(self.item_table.tentative_view() == old(self).item_table.tentative_view().update(item_index as int, *item).delete(old_entry.item_index as int));

            // Create a crash predicate for the append operation and prove that it ensures the append
            // will be crash consistent.
            let ghost crash_pred = |s: Seq<u8>| {
                &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
            };

            let ghost pre_append_self = *self;
            // 5. Append the log entry to the log
            self.append_log_entry_helper(Ghost(*old(self)), log_entry, Ghost(crash_pred), Tracked(perm))?;

            proof {
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).powerpm@, self.powerpm@, self.version_metadata, self.overall_metadata
                );
//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));  
                              
                // We have to prove that each component's invariant holds after appending the new log entry,
                // which is straightforward because they held beforehand and the append operation does 
                // not modify any of their bytes.
                assert(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat) == get_subregion_view(old(self).powerpm@, 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                assert(get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                    self.overall_metadata.list_area_size as nat) == get_subregion_view(old(self).powerpm@, 
                    self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat));
                assert(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat) == get_subregion_view(pre_append_self.powerpm@, 
                    self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat));

                lemma_appending_log_entry_preserves_log_entries_do_not_modify_free_main_table_entries(
                    old(self).log@.physical_op_list,
                    log_entry@,
                    self.main_table.free_indices(),
                    self.overall_metadata
                );

                // Prove that all crash states still recover to the current state. We already know this for each 
                // component, since it's part of their invariants, so we just need to prove that it's true 
                // for the whole KV store as well.
                self.lemma_if_every_component_recovers_to_its_current_state_then_self_does();
                self.lemma_tentative_view_after_appending_update_item_log_entry_includes_new_log_entry(pre_append_self, offset, 
                    old_entry.item_index, item_index, *item, log_entry, pre_append_tentative_view_bytes);

                assert(self.item_table.tentative_valid_indices() == 
                    old(self).item_table.tentative_valid_indices().remove(old_entry.item_index).insert(item_index));
            }

            // 6. Update the main table's outstanding entries to reflect the item index update.
            // The item table has already been updated
            self.update_outstanding_item_index_in_main_table(old_entry, key, offset, item_index);

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
                get_subregion_view(pm, start, len).durable_state == extract_bytes(pm.durable_state, start, len)
        {
            assert(get_subregion_view(pm, start, len).durable_state =~= extract_bytes(pm.durable_state, start, len));
        }

        pub fn tentative_delete(
            &mut self,
            index: u64,
            Tracked(perm): Tracked<&Perm>
        ) -> (result: Result<(), KvError<K>>)
            requires
                old(self).valid(),
                old(self).tentative_view() is Some,
                old(self).tentative_view().unwrap().contains_key(index as int),
                !old(self).transaction_committed(),
                perm.check_permission(old(self).powerpm_view().durable_state),
                Self::physical_recover(old(self).powerpm_view().durable_state, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                forall |s| {
                    &&& Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm_view().durable_state)
                } ==> #[trigger] perm.check_permission(s),
                Self::physical_recover(old(self).powerpm_view().durable_state, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).powerpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    &&& tentative_view matches Some(tentative_view)
                    &&& tentative_view.contains_key(index as int)
                }),
            ensures 
                self.valid(),
                self.constants() == old(self).constants(),
                !self.transaction_committed(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                self@ == old(self)@,
                self.tentative_view_inv(),
                perm.check_permission(self.powerpm_view().durable_state),
                match result {
                    Ok(()) => {
                        self.tentative_view() == Some(old(self).tentative_view().unwrap().delete(index as int).unwrap())
                    }
                    Err(e) => {
                        // transaction has been aborted due to an error in the log
                        // this drops all outstanding modifications to the kv store
                        let tentative_view = self.tentative_view();
                        &&& e is CRCMismatch || e is OutOfSpace
                        &&& tentative_view == Self::physical_recover_given_log(self.powerpm_view().read_state, 
                              self.spec_overall_metadata(), AbstractOpLogState::initialize())
                        &&& self@ == old(self)@
                        &&& Some(self@) == self.tentative_view()
                        &&& e is CRCMismatch ==> !self.constants().impervious_to_corruption()
                    }
                }
        {
            assert(forall |idx: u64| old(self).main_table.free_list().contains(idx) ==> 
                idx < self.overall_metadata.num_keys);
            
            let pm = self.powerpm.get_pm_region_ref();
            let main_table_subregion = PersistentMemorySubregion::new(
                pm,
                self.overall_metadata.main_table_addr,
                Ghost(self.overall_metadata.main_table_size as nat)
            );

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);

                // These asserts establish that the main table subregion recovers properly, which is 
                // a precondition of some of the fns that handle aborted transactions later on.
                let main_table_subregion_view = get_subregion_view(self.powerpm@,
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let ghost old_tentative_view_bytes = apply_physical_log_entries(old(self).powerpm@.read_state, old(self).log@.physical_op_list).unwrap();
                let ghost old_tentative_main_table_view = parse_main_table::<K>(extract_bytes(old_tentative_view_bytes, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat), self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size).unwrap();
                assert(parse_main_table::<K>(main_table_subregion_view.durable_state, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) is Some);
//                assert(main_table_subregion_view.can_crash_as(main_table_subregion_view.read_state));
//                assert(main_table_subregion_view.flush() == get_subregion_view(self.powerpm@.flush(),
//                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
            }

            // We have to read the current item index from the entry so that we can 
            // properly deallocate it later.
            let (key, metadata) = match self.main_table.get_key_and_metadata_entry_at_index(
                &main_table_subregion, pm, index, Ghost(self.overall_metadata)) 
            {
                Ok((key, metadata)) => (key, metadata),
                Err(e) => {
                    self.general_abort_after_failed_operation(Ghost(*old(self)), Tracked(perm));
                    return Err(e);
                }
            };
            let item_index = metadata.item_index;
            assert(!self.item_table.free_list().contains(item_index));

            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                self.log@.physical_op_list).unwrap();
            proof { 
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);
                
                // the current item index we read from PM is valid in the tentative view
                assert(self.main_table.tentative_view().durable_main_table[index as int] is Some);
                assert(self.main_table.tentative_view().durable_main_table[index as int].unwrap().item_index() == item_index);

                // the current durable state recovers to the current main table view
                assert(get_subregion_view(self.powerpm@, main_table_subregion.start(), main_table_subregion.len()).durable_state =~=
                    extract_bytes(self.powerpm@.durable_state, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat));
                assert(parse_main_table::<K>(get_subregion_view(self.powerpm@, main_table_subregion.start(), main_table_subregion.len()).durable_state,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@)) 
                by {
//                        lemma_persistent_memory_view_can_crash_as_committed(
//                            get_subregion_view(self.powerpm@, main_table_subregion.start(), main_table_subregion.len()));
                }
            }

            // To tentatively delete a record, we need to obtain a log entry representing 
            // its deletion and tentatively append it to the operation log.
            let log_entry = self.create_delete_log_entry_helper(index, Ghost(tentative_view_bytes), Tracked(perm));

            proof {
                // Before appending to the actual log, prove that if we replay the old log + the new entry on 
                // the current bytes, we get the expected final state. Then, after the real append, we only have 
                // to prove that the bytes on PM recover to the same tentative state.
                let new_log = self.log@.tentatively_append_log_entry(log_entry@);

                lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(self.powerpm@.read_state,
                    self.version_metadata, self.overall_metadata, new_log.physical_op_list);

                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state, new_log.physical_op_list);
                let new_main_table_region = extract_bytes(new_tentative_bytes.unwrap(), 
                    self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                let new_main_table_view = parse_main_table::<K>(new_main_table_region,
                    self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size);
                assert(new_main_table_view == self.main_table.tentative_view().delete(index as int));
            }
    
            let ghost crash_pred = |s: Seq<u8>| {
                &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
            };

            self.append_log_entry_helper(Ghost(*old(self)), log_entry, Ghost(crash_pred), Tracked(perm))?;

            proof {
                // Prove that the tentative views obtained by applying the new log 
                // to the pre- and post-append bytes are the same, since the only
                // thing we changed is the log. This lets Verus automatically dispatch
                // some proofs later, e.g., about the tentative state after the 
                // tentative delete operation is completed
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                        self.log@.physical_op_list);
                let old_tentative_bytes = apply_physical_log_entries(old(self).powerpm@.read_state,
                    self.log@.physical_op_list);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);
                lemma_log_replay_preserves_size(old(self).powerpm@.read_state, self.log@.physical_op_list);
                Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old(self).powerpm@.read_state,
                    self.powerpm@.read_state, self.log@.physical_op_list, self.version_metadata, self.overall_metadata);
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(old_tentative_bytes.unwrap(),
                    new_tentative_bytes.unwrap(), self.version_metadata, self.overall_metadata);
            }

            let ghost item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat);

            self.main_table.tentatively_deallocate_entry(Ghost(main_table_subregion.view(pm)),
                index, *metadata, *key, Ghost(self.overall_metadata));
            self.item_table.tentatively_deallocate_item(Ghost(item_table_subregion_view), item_index, Ghost(self.overall_metadata));

            assert(self.inv()) by {
                assert(main_table_subregion.view(pm) ==
                       get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                          self.overall_metadata.main_table_size as nat));
                lemma_if_views_dont_differ_in_metadata_area_then_metadata_unchanged_on_crash(
                    old(self).powerpm@, self.powerpm@, self.version_metadata, self.overall_metadata
                );
            }

            assert(self.tentative_view_inv()) by {
                let new_tentative_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                        self.log@.physical_op_list).unwrap();
                let new_tentative_item_table_bytes = extract_bytes(new_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                let old_tentative_bytes = apply_physical_log_entries(old(self).powerpm@.read_state,
                        old(self).log@.physical_op_list).unwrap();
                let old_tentative_item_table_bytes = extract_bytes(old_tentative_bytes, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);

                assert(self.item_table.tentative_view() == old(self).item_table.tentative_view().delete(item_index as int));
                self.lemma_item_table_unchanged_by_log_replay(*old(self), old_tentative_bytes, new_tentative_bytes);
                assert(new_tentative_item_table_bytes == old_tentative_item_table_bytes);
                assert(self.tentative_item_table() == old(self).tentative_item_table().delete(item_index as int));
            }

            assert(self.tentative_view() == Some(old(self).tentative_view().unwrap().delete(index as int).unwrap()));

            Ok(())
        }

        proof fn lemma_if_every_component_recovers_to_its_current_state_then_self_does(self)
            requires
                !self.transaction_committed(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr),
                self.powerpm.inv(),
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
                self.main_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                                                       self.overall_metadata.main_table_size as nat),
                                    self.overall_metadata),
                self.item_table.inv(get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                                                       self.overall_metadata.item_table_size as nat),
                                    self.overall_metadata),
                /* REMOVED UNTIL WE IMPLEMENT LISTS
                self.durable_list.inv(get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                                                         self.overall_metadata.list_area_size as nat),
                                      self.main_table@, self.overall_metadata),
                */
                self.version_metadata == deserialize_version_metadata(self.powerpm@.durable_state),
                self.overall_metadata == deserialize_overall_metadata(
                    self.powerpm@.durable_state,
                    self.version_metadata.overall_metadata_addr
                ),
                self.main_table@.valid_item_indices() == self.item_table.durable_valid_indices(),
            ensures
                self.inv_mem(self.powerpm@.durable_state),
        {
            let overall_metadata = self.overall_metadata;
            assert(self.inv_mem(self.powerpm@.durable_state)) by {
                self.powerpm.lemma_inv_implies_view_valid();
                let s = self.powerpm@.durable_state;
                assert(self.version_metadata == deserialize_version_metadata(s));
                assert(self.overall_metadata == deserialize_overall_metadata(
                    s,
                    self.version_metadata.overall_metadata_addr
                ));
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                assert(UntrustedOpLog::<K, L>::recover(s, self.version_metadata, self.overall_metadata) ==
                       Some(AbstractOpLogState::initialize()));
                assert(apply_physical_log_entries(s, AbstractOpLogState::initialize().physical_op_list) =~=
                       Some(s));
            }
        }

        proof fn lemma_commit_log_precondition(
            self,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            perm: &Perm,
        )
            requires 
                self.valid(),
                perm.check_permission(self.powerpm@.durable_state),
                forall |s| crash_pred(s) ==> perm.check_permission(s),
                forall |s: Seq<u8>| {
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                    &&& {
                        ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                        ||| Self::physical_recover(s, self.version_metadata, self.overall_metadata) ==
                            self.tentative_view()
                    }
                } <==> #[trigger] crash_pred(s),
                self.tentative_view() is Some,
                !self.transaction_committed(),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata,
                                       self.overall_metadata) == Some(self@),
                self.spec_num_log_entries_in_current_transaction() > 0,
                !self.transaction_committed(),
                no_outstanding_writes_to_version_metadata(self.powerpm@),
                no_outstanding_writes_to_overall_metadata(self.powerpm@,
                                                          self.version_metadata.overall_metadata_addr as int),
                self.powerpm@.len() >= VersionMetadata::spec_size_of(),
            ensures
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat,
                                                       self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) ==
                        Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                        Some(AbstractOpLogState::initialize())
                } ==> #[trigger] crash_pred(s2),
                forall |s2: Seq<u8>| {
                    let crash_state = self.powerpm@.durable_state;
                    &&& crash_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(crash_state, s2,
                                                       self.overall_metadata.log_area_addr as nat,
                                                       self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                          Some(AbstractOpLogState::initialize())
                } ==> perm.check_permission(s2),
                forall |s2: Seq<u8>| {
                    let flushed_state = self.powerpm@.read_state;
                    &&& flushed_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(flushed_state, s2,
                                                       self.overall_metadata.log_area_addr as nat,
                                                       self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                           Some(self.log@.commit_op_log())
                } ==> perm.check_permission(s2),
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
         
            self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
            lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);

            // Prove that the crash predicate satisfies the preconditions about it, which specify how we can crash
            // before and after `commit_log` flushes the device.
            assert forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(AbstractOpLogState::initialize())
            } implies #[trigger] crash_pred(s2) by { 
                self.lemma_durable_kv_satisfies_crash_condition_with_init_op_log(s1, s2, crash_pred); 
            }
            
            assert forall |s2: Seq<u8>| {
                let flushed_state = self.powerpm@.read_state;
                &&& flushed_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(flushed_state, s2, self.overall_metadata.log_area_addr as nat,
                                                   self.overall_metadata.log_area_size as nat)
                &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@.commit_op_log())
            } implies perm.check_permission(s2) by {
                let flushed_state = self.powerpm@.read_state;
                  // The CDB made it to storage.
                  // In this case, the whole KV store recovers to its tentative view. 
                  let committed_log = self.log@.commit_op_log();

                  Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(
                      flushed_state, s2, committed_log.physical_op_list, self.version_metadata,
                      self.overall_metadata);
                  lemma_log_replay_preserves_size(s2, committed_log.physical_op_list);
                  let flushed_state_with_log_installed =
                    apply_physical_log_entries(flushed_state, committed_log.physical_op_list).unwrap();
                let s2_with_log_installed =
                    apply_physical_log_entries(s2, committed_log.physical_op_list).unwrap();

                assert(states_differ_only_in_log_region(flushed_state_with_log_installed, s2_with_log_installed, 
                                                        self.overall_metadata.log_area_addr as nat,
                                                        self.overall_metadata.log_area_size as nat));
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    flushed_state_with_log_installed, s2_with_log_installed, self.version_metadata,
                    self.overall_metadata
                );

                assert(version_and_overall_metadata_match_deserialized(s2, self.powerpm@.durable_state)) by {
                    // broadcast use pmcopy_axioms;
                    lemma_establish_extract_bytes_equivalence(s2, self.powerpm@.durable_state);
                }
            }
            
            assert forall |s2: Seq<u8>| {
                let crash_state = self.powerpm@.durable_state;
                &&& crash_state.len() == s2.len() 
                &&& states_differ_only_in_log_region(crash_state, s2, self.overall_metadata.log_area_addr as nat,
                                                   self.overall_metadata.log_area_size as nat)
                &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                       Some(AbstractOpLogState::initialize())
            } implies perm.check_permission(s2) by {
                let crash_state = self.powerpm@.durable_state;
                // The CDB did not make it to storage.
                assert(UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                       Some(AbstractOpLogState::initialize()));
                self.lemma_durable_kv_satisfies_crash_condition_with_init_op_log(crash_state, s2, crash_pred);
            }
        }

        proof fn lemma_can_clear_op_log_after_commit(
            self,
            old_self: Self,
            pre_log_install_powerpm: PoWERPersistentMemoryRegion<Perm, PM>,
            pre_log_install_op_log: AbstractOpLogState,
            crash_pred: spec_fn(Seq<u8>) -> bool,
            perm: &Perm,
        )
            requires
                self.powerpm.inv(),
                pre_log_install_powerpm.inv(),
                self.log.inv(pre_log_install_powerpm@, self.version_metadata, self.overall_metadata),
                forall |s: Seq<u8>| {
                    &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@) 
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                } <==> #[trigger] crash_pred(s),
                forall |s| #[trigger] crash_pred(s) ==> perm.check_permission(s),
                self.powerpm@.flush_predicted(),
                pre_log_install_powerpm@.flush_predicted(),
                crash_pred(self.powerpm@.durable_state),
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.powerpm@.len() == pre_log_install_powerpm@.len(),
                self.powerpm@.len() == self.overall_metadata.region_size,
                self.powerpm@.len() == pre_log_install_powerpm@.len(),
                self.transaction_committed(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr),
                UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self.log@),
                AbstractPhysicalOpLogEntry::log_inv(self.log@.physical_op_list, self.version_metadata, self.overall_metadata),
                extract_bytes(pre_log_install_powerpm@.durable_state, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat) ==
                    extract_bytes(self.powerpm@.durable_state, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat),
                Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == 
                    Self::physical_recover_given_log(self.powerpm@.durable_state, self.overall_metadata, AbstractOpLogState::initialize()),
                deserialize_version_metadata(self.powerpm@.durable_state) == self.version_metadata,
                forall |s| {
                    &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                    &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
                } <==> #[trigger] crash_pred(s),
            ensures 
                forall |s2: Seq<u8>| {
                    let flushed_state = self.powerpm@.read_state;
                    &&& flushed_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(s2, flushed_state,
                                                       self.overall_metadata.log_area_addr as nat,
                                                       self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                           Some(self.log@)
                } ==> #[trigger] crash_pred(s2),
                forall |s2: Seq<u8>| {
                    let crash_state = self.powerpm@.durable_state;
                    &&& crash_state.len() == s2.len() 
                    &&& states_differ_only_in_log_region(s2, crash_state,
                                                       self.overall_metadata.log_area_addr as nat,
                                                       self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) ==
                          Some(AbstractOpLogState::initialize())
                } ==> #[trigger] crash_pred(s2),
                forall |s1: Seq<u8>, s2: Seq<u8>| {
                    &&& s1.len() == s2.len() 
                    &&& #[trigger] crash_pred(s1)
                    &&& states_differ_only_in_log_region(s1, s2, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat)
                    &&& UntrustedOpLog::<K, L>::recover(s1, self.version_metadata, self.overall_metadata) == Some(self.log@)
                    &&& UntrustedOpLog::<K, L>::recover(s2, self.version_metadata, self.overall_metadata) == Some(self.log@)
                } ==> #[trigger] crash_pred(s2),
                self.log.inv(self.powerpm@, self.version_metadata, self.overall_metadata),
                crash_pred(self.powerpm@.durable_state),
                UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == Some(self.log@),
        {
            let current_mem = self.powerpm@.durable_state;
            let old_mem_with_log_installed = apply_physical_log_entries(pre_log_install_powerpm@.durable_state, 
                pre_log_install_op_log.physical_op_list).unwrap();
            let pre_install_subregion = get_subregion_view(pre_log_install_powerpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);
            let current_subregion = get_subregion_view(self.powerpm@, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);
            let pre_install_extract_bytes = extract_bytes(pre_log_install_powerpm@.durable_state, self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat);

//            lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(self.powerpm@);
//            assert(forall |s| self.powerpm@.can_crash_as(s) ==> s == self.powerpm@.durable_state);

            // Next, we need to prove that the log subregions of the pre-install PM and current PM
            // are identical, so that we can prove that the op log invariant holds after log install.
            assert forall |addr: int| 0 <= addr < self.overall_metadata.log_area_size implies 
                views_match_at_addr(pre_install_subregion, current_subregion, addr)
            by {
//                assert(pre_install_subregion.state[addr].state_at_last_flush == pre_install_extract_bytes[addr]);
//                assert(pre_install_subregion.state[addr].outstanding_write is None);
//                assert(current_subregion.state[addr].outstanding_write is None);
            }
            assert(pre_install_subregion == current_subregion);
            self.log.lemma_same_op_log_view_preserves_invariant(pre_log_install_powerpm, self.powerpm, self.version_metadata, self.overall_metadata);

            // By now we've also met the preconditions of this lemma that proves that we can safely 
            // clear the log
            Self::lemma_clear_log_is_crash_safe(self.powerpm, self.log, self.version_metadata,
                self.overall_metadata, crash_pred, self@, perm);
        }


        // Commits all pending updates by committing the log and applying updates to 
        // each durable component.
        #[verifier::rlimit(30)] // TODO @hayley
        pub fn commit(
            &mut self,
            Tracked(perm): Tracked<&Perm>
        ) -> (result: Result<(), KvError<K>>)
            requires 
                old(self).valid(),
                !old(self).transaction_committed(),
                perm.check_permission(old(self).powerpm_view().durable_state),
                Self::physical_recover(old(self).powerpm_view().durable_state, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@),
                forall |s| {
                    &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm_view().durable_state)
                    &&& {
                        ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                        ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == old(self).tentative_view()
                    }
                } ==> #[trigger] perm.check_permission(s),
                no_outstanding_writes_to_version_metadata(old(self).powerpm_view()),
                no_outstanding_writes_to_overall_metadata(old(self).powerpm_view(), old(self).spec_overall_metadata_addr() as int),
                old(self).powerpm_view().len() >= VersionMetadata::spec_size_of(),
                ({
                    let tentative_view = old(self).tentative_view();
                    tentative_view is Some
                }),
                old(self).spec_num_log_entries_in_current_transaction() > 0,
                perm.check_permission(old(self).powerpm_view().durable_state),
            ensures
                self.valid(),
                self.constants() == old(self).constants(),
                self.spec_overall_metadata() == old(self).spec_overall_metadata(),
                perm.check_permission(self.powerpm_view().durable_state),
                !self.transaction_committed(), // only used internally
                match result {
                    Ok(()) => {
                        // The old tentative view is now our current state
                        let old_tentative_view = old(self).tentative_view();
                        &&& old_tentative_view matches Some(old_tentative_view)
                        &&& self@ == old_tentative_view
                        &&& self.tentative_view() == Some(self@)
                    }
                    Err(KvError::CRCMismatch) => {
                        let tentative_view = self.tentative_view();
                        &&& tentative_view == Self::physical_recover_given_log(self.powerpm_view().read_state, 
                            self.spec_overall_metadata(), AbstractOpLogState::initialize())
                        &&& self@ == old(self)@
                        &&& self.tentative_view() == Some(old(self)@)
                        &&& !self.constants().impervious_to_corruption()
                    }
                    Err(e) => {
                        // Transaction has been aborted due to an error in the log.
                        // This can happen during commit if we don't have enough space to 
                        // write the CRC when committing the oplog.
                        // All outstanding writes to the KV store are dropped.
                        let tentative_view = self.tentative_view();
                        &&& e is OutOfSpace || e is LogErr
                        &&& tentative_view == Self::physical_recover_given_log(self.powerpm_view().read_state, 
                            self.spec_overall_metadata(), AbstractOpLogState::initialize())
                        &&& self@ == old(self)@
                        &&& self.tentative_view() == Some(old(self)@)
                    }
                }
        {
            hide(MainTable::opaquable_inv);
            hide(DurableItemTable::opaquable_inv);
         
            let ghost tentative_view_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();

            // 1. Create the crash predicate for the commit operation.
            // This predicate will allow either the current durable state or the current tentative state
            let ghost crash_pred = |s: Seq<u8>| {
                &&& version_and_overall_metadata_match_deserialized(s, old(self).powerpm@.durable_state)
                    &&& {
                        ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == Some(old(self)@)
                        ||| Self::physical_recover(s, old(self).spec_version_metadata(), old(self).spec_overall_metadata()) == old(self).tentative_view()
                    }
            };

            proof {
                self.log.lemma_reveal_opaque_op_log_inv(self.powerpm, self.version_metadata, self.overall_metadata);
                lemma_log_replay_preserves_size(self.powerpm@.read_state, self.log@.physical_op_list);
                self.lemma_commit_log_precondition(crash_pred, perm);

//                assert(self.powerpm@.can_crash_as(self.powerpm@.durable_state));
                assert(forall |s| crash_pred(s) ==> perm.check_permission(s));

                assert(crash_pred(self.powerpm@.durable_state)) by {
                    broadcast use pmcopy_axioms;
//                    lemma_wherever_no_outstanding_writes_persistent_memory_view_can_only_crash_as_committed(self.powerpm@);
//                    lemma_establish_extract_bytes_equivalence(s, self.powerpm@.durable_state);
                }
            }

            // 2. Commit the op log
            let ghost pre_self = *self;
            match self.log.commit_log(&mut self.powerpm, self.version_metadata, 
                                      self.overall_metadata, Ghost(crash_pred), Tracked(perm)) 
            {
                Ok(()) => {}
                Err(e) => {
                    proof {
                        let main_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                            self.overall_metadata.main_table_size as nat);
                        let old_main_table_subregion_view = get_subregion_view(old(self).powerpm@, self.overall_metadata.main_table_addr as nat,
                            self.overall_metadata.main_table_size as nat);
                        assert(old_main_table_subregion_view.durable_state =~= main_table_subregion_view.durable_state);
//                        assert(old_main_table_subregion_view.flush() == main_table_subregion_view);
//                        assert(old_main_table_subregion_view.can_crash_as(main_table_subregion_view.durable_state));
                        assert(parse_main_table::<K>(main_table_subregion_view.durable_state, self.overall_metadata.num_keys, 
                            self.overall_metadata.main_table_entry_size) is Some);
                    }
                    self.abort_after_failed_op_log_operation(Ghost(*old(self)), Ghost(pre_self), Tracked(perm));
                    return Err(e);
                }
            }

            let ghost abstract_op_log = UntrustedOpLog::<K, L>::recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata).unwrap();

            // 3. Install the physical log
            proof {
                // First, prove various facts about what will happen if we install the log.

                let phys_log_view = PhysicalOpLogEntry::vec_view(self.pending_updates);
                let old_mem_with_log_installed = apply_physical_log_entries(old(self).powerpm@.read_state, phys_log_view).unwrap();
                let new_mem_with_log_installed = apply_physical_log_entries(self.powerpm@.durable_state, phys_log_view).unwrap();

                // Prove that the logged updates tracked in volatile memory constitute a valid log (which implies
                // replaying the log will succeed and result in a valid KV store state)
                assert(PhysicalOpLogEntry::log_inv(self.pending_updates, self.version_metadata, self.overall_metadata)) by {
                    reveal(MainTable::opaquable_inv);
                    reveal(DurableItemTable::opaquable_inv);
                    PhysicalOpLogEntry::lemma_abstract_log_inv_implies_concrete_log_inv(self.pending_updates,
                        self.version_metadata, self.overall_metadata);
                }

                // If we replay the concrete log in volatile memory and the ghost log, the resulting bytes
                // in each non-log region will match
                assert(abstract_op_log.physical_op_list == phys_log_view);
                Self::lemma_applying_same_log_preserves_states_differ_only_in_log_region(old(self).powerpm@.read_state, self.powerpm@.durable_state,
                    phys_log_view, self.version_metadata, self.overall_metadata);
                lemma_log_replay_preserves_size(self.powerpm@.durable_state, phys_log_view);
                assert(states_differ_only_in_log_region(old_mem_with_log_installed, new_mem_with_log_installed, 
                    self.overall_metadata.log_area_addr as nat, self.overall_metadata.log_area_size as nat));
                lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(
                    old_mem_with_log_installed, new_mem_with_log_installed, self.version_metadata, self.overall_metadata);

                // If we replay the log, we will obtain the current tentative view
                assert(Self::physical_recover(self.powerpm@.durable_state, self.version_metadata, self.overall_metadata) == old(self).tentative_view());
                
                // Prove that version and overall metadata have not been changed
                assert(version_and_overall_metadata_match_deserialized(self.powerpm@.durable_state, old(self).powerpm@.durable_state)) by {
                    broadcast use pmcopy_axioms;
                    lemma_establish_extract_bytes_equivalence(self.powerpm@.durable_state, old(self).powerpm@.durable_state);
                }
            }

            let ghost pre_log_install_powerpm = self.powerpm;

            Self::install_log(&mut self.powerpm, self.version_metadata, self.overall_metadata, &self.pending_updates, Tracked(perm));

            proof {
                // Some functions/proofs use `extract_bytes`  and some use `get_subregion_view` 
                // (depending on whether they need PersistentMemoryRegionView information or not)
                // so we first have to prove that these are equivalent.
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.powerpm@, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.powerpm@, self.overall_metadata.item_table_addr as nat, self.overall_metadata.item_table_size as nat);
                Self::lemma_committed_subregion_equal_to_extracted_bytes(self.powerpm@, self.overall_metadata.list_area_addr as nat, self.overall_metadata.list_area_size as nat);        
                            
                let subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);

                let old_subregion_view = get_subregion_view(old(self).powerpm@, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat); 
                assert(parse_main_table::<K>(old_subregion_view.durable_state, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) is Some);

                let tentative_bytes_main_table_region = extract_bytes(tentative_view_bytes, self.overall_metadata.main_table_addr as nat,
                    self.overall_metadata.main_table_size as nat);
            
                let durable_state_bytes = old(self).powerpm@.durable_state;
                let durable_main_table_region = extract_bytes(durable_state_bytes, self.overall_metadata.main_table_addr as nat, self.overall_metadata.main_table_size as nat);
                assert(durable_main_table_region == old_subregion_view.durable_state);
                
            }

            // 4. Update ghost state and finalize pending (de)allocations.
            self.main_table.finalize_main_table(Ghost(old(self).main_table), Ghost(old(self).powerpm@),
                Ghost(self.powerpm@), Ghost(self.overall_metadata));
            assert(self.item_table.opaquable_inv(self.overall_metadata, self.item_table.durable_valid_indices())) by {
                reveal(DurableItemTable::opaquable_inv);
            }
            self.item_table.finalize_item_table(Ghost(old(self).item_table), Ghost(self.powerpm@), 
                Ghost(self.overall_metadata));

         /* REMOVED UNTIL WE IMPLEMENT LISTS
            // TODO: replace with finalize fn that finishes (de)allocs and updates ghost state
            self.durable_list.update_ghost_state_to_current_bytes(Ghost(self.powerpm@), Ghost(self.overall_metadata), 
                Ghost(self.main_table@));
         */

            // We now need a more restrictive crash predicate, as there are fewer legal crash states now that 
            // we have replayed the log. It's still the case that clear_log_crash_pred(s) ==> perm.check_permission(s)
            let ghost clear_log_crash_pred = |s: Seq<u8>| {
                &&& Self::physical_recover(s, self.version_metadata, self.overall_metadata) == Some(self@)
                &&& version_and_overall_metadata_match_deserialized(s, self.powerpm@.durable_state)
            };

            // 5. Clear the log
            proof {
                // Next, prove that we can safely clear the log.
                self.lemma_can_clear_op_log_after_commit(*old(self), pre_log_install_powerpm, 
                    abstract_op_log, clear_log_crash_pred, &perm);

                let durable_item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                    self.overall_metadata.item_table_size as nat);
                let durable_list_area_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                    self.overall_metadata.list_area_size as nat);

                // Establish some facts about the possible crash states of the item table and list area
                // to reestablish their invariants
                // The assertions and lemmas here seem redundant, but the assertions appear to have an impact on a later proof,
                // and the lemmas are required to reestablish the invariants.
//                assert(durable_item_table_subregion_view.can_crash_as(durable_item_table_subregion_view.durable_state));
//                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_item_table_subregion_view);
                   /* REMOVED UNTIL WE IMPLEMENT LISTS
                assert(durable_list_area_subregion_view.can_crash_as(durable_list_area_subregion_view.durable_state));
                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_list_area_subregion_view);
                   */
            }
            
            let ghost pre_clear_powerpm = self.powerpm@;
            self.log.clear_log(&mut self.powerpm, self.version_metadata, self.overall_metadata, Ghost(clear_log_crash_pred), Tracked(perm))?;
            self.pending_updates = Vec::new();
            
            proof {
                // clearing the log does not change the view of any other parts of the KV store
                self.lemma_view_and_components_unchanged(pre_clear_powerpm);

                // The new durable and tentative states are equal.
                let new_durable_state_bytes = self.powerpm@.durable_state;
                let new_tentative_state_bytes = apply_physical_log_entries(self.powerpm@.read_state,
                    self.log@.physical_op_list).unwrap();
                assert(new_durable_state_bytes == new_tentative_state_bytes);

                // The log and the local pending lists are both empty
                assert(self.log@.physical_op_list.len() == 0);
                assert(self.pending_updates@.len() == 0);
                assert(PhysicalOpLogEntry::vec_view(self.pending_updates) == self.log@.physical_op_list);
                
                // Version and overall metadata remain the same in all current crash states.
                assert(no_outstanding_writes_to_version_metadata(self.powerpm@));
                assert(no_outstanding_writes_to_overall_metadata(self.powerpm@, self.version_metadata.overall_metadata_addr as int));
                assert(self.inv_mem(self.powerpm@.durable_state));
//                lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(self.powerpm@);
//                assert(forall |s| #[trigger] self.powerpm@.can_crash_as(s) ==> self.inv_mem(s));

                // these all require extensional equality
                assert(self.tentative_main_table() =~= self.main_table.tentative_view()) by {
                    reveal(MainTable::opaquable_inv);
                }
                assert(self.tentative_item_table() =~= self.item_table.tentative_view()) by {
                    reveal(DurableItemTable::opaquable_inv);
                }
                assert(self.main_table.tentative_view().valid_item_indices() =~= self.item_table.tentative_valid_indices());
                assert(self.main_table@.valid_item_indices() =~= self.item_table.durable_valid_indices());
            }
            
            Ok(())
        }

        proof fn lemma_view_and_components_unchanged(
            self,
            pre_state: PersistentMemoryRegionView,
        )
            requires 
                views_differ_only_in_log_region(self.powerpm@, pre_state, self.overall_metadata.log_area_addr as nat,
                    self.overall_metadata.log_area_size as nat),
                ({
                    let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    parse_main_table::<K>(pre_durable_main_table_subregion_view.durable_state, 
                        self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@)
                }),
                self.powerpm@.flush_predicted(),
                pre_state.flush_predicted(),
                overall_metadata_valid::<K, I, L>(self.overall_metadata, self.version_metadata.overall_metadata_addr),
                pre_state.len() == self.powerpm@.len(),
                self.powerpm@.len() == self.overall_metadata.region_size,
            ensures 
                ({
                    let durable_main_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                        self.overall_metadata.main_table_size as nat);
                    let durable_item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                    let pre_durable_item_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.item_table_addr as nat,
                        self.overall_metadata.item_table_size as nat);
                    let durable_list_area_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                        self.overall_metadata.list_area_size as nat);
                    let pre_durable_list_area_subregion_view = get_subregion_view(pre_state, self.overall_metadata.list_area_addr as nat,
                        self.overall_metadata.list_area_size as nat);
                    &&& pre_durable_main_table_subregion_view == durable_main_table_subregion_view
                    &&& pre_durable_item_table_subregion_view == durable_item_table_subregion_view
                    &&& pre_durable_list_area_subregion_view == durable_list_area_subregion_view
//                    &&& durable_main_table_subregion_view.can_crash_as(pre_durable_main_table_subregion_view.durable_state)
                    &&& parse_main_table::<K>(durable_main_table_subregion_view.durable_state, self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@)
                }),
                extracted_regions_match(self.powerpm@.durable_state, pre_state.durable_state, self.overall_metadata),
                deserialize_version_metadata(self.powerpm@.durable_state) == deserialize_version_metadata(pre_state.durable_state),
                deserialize_overall_metadata(self.powerpm@.durable_state, self.version_metadata.overall_metadata_addr) == 
                        deserialize_overall_metadata(pre_state.durable_state, self.version_metadata.overall_metadata_addr),

        {
            let durable_main_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);
            let pre_durable_main_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.main_table_addr as nat,
                self.overall_metadata.main_table_size as nat);
            let durable_item_table_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat);
            let pre_durable_item_table_subregion_view = get_subregion_view(pre_state, self.overall_metadata.item_table_addr as nat,
                self.overall_metadata.item_table_size as nat);
            let durable_list_area_subregion_view = get_subregion_view(self.powerpm@, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);
            let pre_durable_list_area_subregion_view = get_subregion_view(pre_state, self.overall_metadata.list_area_addr as nat,
                self.overall_metadata.list_area_size as nat);

            lemma_non_log_components_match_when_states_differ_only_in_log_region::<K, I, L>(pre_state.durable_state,
                self.powerpm@.durable_state, self.version_metadata, self.overall_metadata);

//            assert(pre_durable_main_table_subregion_view.state == durable_main_table_subregion_view.state);
//            assert(pre_durable_item_table_subregion_view.state == durable_item_table_subregion_view.state);
//            assert(pre_durable_list_area_subregion_view.state == durable_list_area_subregion_view.state);
        
//            assert(durable_main_table_subregion_view.can_crash_as(pre_durable_main_table_subregion_view.durable_state));
//            lemma_if_no_outstanding_writes_then_persistent_memory_view_can_only_crash_as_committed(durable_main_table_subregion_view);
            assert(parse_main_table::<K>(durable_main_table_subregion_view.durable_state, 
                self.overall_metadata.num_keys, self.overall_metadata.main_table_entry_size) == Some(self.main_table@));
        }
    }     
}
