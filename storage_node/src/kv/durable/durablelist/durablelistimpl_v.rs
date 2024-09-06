use crate::kv::durable::durablelist::layout_v::*;
use crate::kv::durable::oplog::{logentry_v::*, oplogimpl_v::*};
use crate::kv::durable::itemtable::itemtableimpl_v::*;
use crate::kv::durable::metadata::{layout_v::*, metadataimpl_v::*};
use crate::kv::durable::util_v::*;
use crate::kv::kvimpl_t::*;
use crate::kv::layout_v::*;
use crate::kv::setup_v::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::traits_t;
use crate::pmem::subregion_v::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub struct TrustedListPermission
    {
        // TODO: how many regions will this use? Probably just one?
        ghost is_state_allowable: spec_fn(Seq<u8>) -> bool
    }

    impl CheckPermission<Seq<u8>> for TrustedListPermission
    {
        closed spec fn check_permission(&self, state: Seq<u8>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }

    impl TrustedListPermission 
    {
         // TODO: REMOVE THIS
         #[verifier::external_body]
         pub proof fn fake_list_perm() -> (tracked perm: Self)
         {
             Self {
                 is_state_allowable: |s| true
             }
         }
    }

    pub struct DurableListElementView<L>
    {
        crc: u64,
        list_element: L
    }

    impl<L> DurableListElementView<L>
    {
        pub closed spec fn new(crc: u64, list_element: L) -> Self 
        {
            Self { crc, list_element }
        }

        pub closed spec fn list_element(self) -> L 
        {
            self.list_element
        }
    }

    // The `lists` field represents the current contents of the list. It abstracts away the physical 
    // nodes of the unrolled linked list that the list is actually stored in, but it may contain
    // tentatively-appended list elements that are not visible yet.
    #[verifier::reject_recursive_types(K)]
    pub struct DurableListView<K, L>
    {
        pub durable_lists: Map<K, Seq<DurableEntry<DurableListElementView<L>>>>,
        pub tentative_lists: Map<K, Seq<DurableEntry<DurableListElementView<L>>>>,
    }

    impl<K, L> DurableListView<K, L>
        where
            K: std::fmt::Debug,
    {
        // pub closed spec fn spec_index(self, key: K) -> Option<Seq<DurableListElementView<L>>>
        // {
        //     if self.lists.contains_key(key) {
        //         Some(self.lists[key])
        //     } else {
        //         None
        //     }
        // }

        pub closed spec fn init() -> Self 
        {
            Self {
                durable_lists: Map::empty(),
                tentative_lists: Map::empty()
            }
        }

        pub closed spec fn new(lists: Map<K, Seq<DurableEntry<DurableListElementView<L>>>>) -> Self 
        {
            Self {
                durable_lists: lists,
                tentative_lists: lists
            }
        }

        // pub closed spec fn insert_key(self, key: K) -> Result<Self, KvError<K>>
        // {
        //     if self.lists.contains_key(key) {
        //         Err(KvError::KeyAlreadyExists)
        //     } else {
        //         Ok(Self {
        //             lists: self.lists.insert(key, Seq::empty()),
        //         })
        //     }
        // }

        // pub closed spec fn insert_list_element(
        //     self,
        //     key: K,
        //     crc: u64,
        //     list_element: L,
        //     index: int
        // ) -> Result<Self, KvError<K>>
        // {
        //     if !self.lists.contains_key(key) {
        //         Err(KvError::KeyNotFound)
        //     } else if index < 0 || index > self.lists[key].len() {
        //         Err(KvError::IndexOutOfRange)
        //     } else {
        //         let new_lists = self.lists[key].update(index, DurableListElementView { crc, list_element });
        //         Ok(Self {
        //             lists: self.lists.insert(key, new_lists),
        //         })
        //     }
        // }

        // pub closed spec fn append_list_element(
        //     self,
        //     key: K,
        //     crc: u64,
        //     list_element: L
        // ) -> Result<Self, KvError<K>>
        // {
        //     if !self.lists.contains_key(key) {
        //         Err(KvError::KeyNotFound)
        //     } else {
        //         let new_lists = self.lists[key].push(DurableListElementView { crc, list_element });
        //         Ok(Self {
        //             lists: self.lists.insert(key, new_lists),
        //         })
        //     }
        // }

        // pub closed spec fn remove_key(
        //     self,
        //     key: K
        // ) -> Result<Self, KvError<K>>
        // {
        //     if !self.lists.contains_key(key) {
        //         Err(KvError::KeyNotFound)
        //     } else {
        //         Ok(Self {
        //             lists: self.lists.remove(key),
        //         })
        //     }
        // }

        // pub closed spec fn trim_lists(
        //     self,
        //     key: K,
        //     trim_length: int
        // ) -> Result<Self, KvError<K>>
        // {
        //     if !self.lists.contains_key(key) {
        //         Err(KvError::KeyNotFound)
        //     } else {
        //         let new_lists = self.lists[key].subrange(trim_length, self.lists[key].len() as int);
        //         Ok(Self {
        //             lists: self.lists.insert(key, new_lists),
        //         })
        //     }
        // }
    }

    pub const NUM_DURABLE_LIST_REGIONS: u64 = 1;

    #[verifier::reject_recursive_types(K)]
    pub struct DurableList<K, L>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug,
    {
        list_node_region_free_list: Vec<u64>,
        // TODO: pending allocations field
        node_size: u64,
        elements_per_node: u64,
        num_nodes: u64,
        state: Ghost<DurableListView<K, L>>
    }

    impl<K, L> DurableList<K, L>
        where
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug,
    {
        pub closed spec fn view(self) -> DurableListView<K, L>
        {
            self.state@
        }

        // TODO
        pub open spec fn inv(self, pm: PersistentMemoryRegionView, main_table_view: MetadataTableView<K>, overall_metadata: OverallMetadata) -> bool
        {
            &&& forall |s| #[trigger] pm.can_crash_as(s) ==>
                    Self::parse_all_lists(main_table_view, s, overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node) == Some(self@)
        }

        pub open spec fn recover(
            mem: Seq<u8>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
            op_log: AbstractOpLogState,
            metadata_table_view: MetadataTableView<K>,
        ) -> Option<DurableListView<K, L>>
        {
            None
            // // TODO: check list node region header for validity? or do we do that later?
            // let list_nodes_mem = Self::replay_log_list_nodes(mem, list_node_size, op_log);
            // Self::parse_all_lists(metadata_table_view, mem, list_node_size, num_list_entries_per_node)
        }

        pub open spec fn replay_log_list_nodes(
            mem: Seq<u8>, 
            node_size: u64, 
            op_log: Seq<LogicalOpLogEntry<L>>, 
        ) -> Seq<u8>
            decreases op_log.len() 
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_list_node_mem(mem, node_size, current_op);
                Self::replay_log_list_nodes(mem, node_size, op_log)
            }
        }

        pub open spec fn apply_log_op_to_list_node_mem(
            mem: Seq<u8>, 
            node_size: u64, 
            op: LogicalOpLogEntry<L>, 
        ) -> Seq<u8>
        {
            match op {
                LogicalOpLogEntry::UpdateListElement { node_index, index_in_node, list_element } => {
                    let node_addr = node_index * node_size;
                    let list_entry_size = L::spec_size_of() + u64::spec_size_of(); // list element + CRC
                    let list_element_slot = node_addr + list_entry_size * index_in_node;
                    let crc_addr = list_element_slot;
                    let list_element_addr = crc_addr + u64::spec_size_of();
                    let new_element_bytes = list_element.spec_to_bytes();
                    let new_crc_bytes = spec_crc_bytes(new_element_bytes);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + u64::spec_size_of() {
                            new_crc_bytes[pos - crc_addr]
                        } else if list_element_addr <= pos < list_element_addr + L::spec_size_of() {
                            new_element_bytes[pos - list_element_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                },
                _ => mem // all other ops do not modify the list node region
            }
        }

        pub open spec fn parse_all_lists(
            metadata_table: MetadataTableView<K>,
            mem: Seq<u8>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        ) -> Option<DurableListView<K, L>> 
        {
            let lists_map = Map::empty();
            // TODO: which table do we want to use here?
            let result = Self::parse_each_list(metadata_table.get_durable_metadata_table(), mem, lists_map, list_node_size, num_list_entries_per_node);
            match result {
                Some(result) => Some(DurableListView::new(result)),
                None => None
            }
        }

        pub proof fn lemma_parse_each_list_succeeds_if_no_valid_metadata_entries(
            metadata_entries: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
            mem: Seq<u8>,
            lists_map: Map<K, Seq<DurableEntry<DurableListElementView<L>>>>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        )
            requires
                forall |i: int| 0 <= i < metadata_entries.len() ==> #[trigger] metadata_entries[i] matches DurableEntry::Invalid,
            ensures 
                Self::parse_each_list(metadata_entries, mem, lists_map, list_node_size, num_list_entries_per_node) is Some 
            decreases
                metadata_entries.len()
        {
            // base case
            if metadata_entries.len() == 0 {
                // trivial
            } else {
                Self::lemma_parse_each_list_succeeds_if_no_valid_metadata_entries(metadata_entries.drop_first(), mem, lists_map, list_node_size, num_list_entries_per_node);
            }
        }

        pub proof fn lemma_parse_all_lists_succeeds_after_record_delete(
            old_main_table_view: MetadataTableView<K>,
            main_table_view: MetadataTableView<K>,
            mem: Seq<u8>,
            index: int,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        )
            requires 
                Self::parse_all_lists(old_main_table_view, mem, list_node_size, num_list_entries_per_node) is Some,
                Some(main_table_view) == old_main_table_view.delete(index),
            ensures 
                Self::parse_all_lists(main_table_view, mem, list_node_size, num_list_entries_per_node) is Some,
        {
            assume(false);
        }

        // Note that here, `metadata_entries` does not represent the metadata table exactly -- it's just 
        // used to help recurse over each metadata entry.
        pub open spec fn parse_each_list(
            metadata_entries: Seq<DurableEntry<MetadataTableViewEntry<K>>>,
            mem: Seq<u8>,
            lists_map: Map<K, Seq<DurableEntry<DurableListElementView<L>>>>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        ) -> Option<Map<K, Seq<DurableEntry<DurableListElementView<L>>>>>
            decreases
                metadata_entries.len()
        {
            if metadata_entries.len() <= 0 {
                Some(lists_map)
            } else {
                let current_entry = metadata_entries[0];
                let metadata_entries = metadata_entries.drop_first();
                // Unlike in the item table, where we build the view and replay the log simultaneously we will apply log entries later; we need to build the lists 
                // before replaying log entries so that log entries can be applied to the table and the list in the correct order
                // TODO: Valid vs. Tentative entry types?
                if let DurableEntry::Valid(current_entry) = current_entry {
                    let recovered_list = Self::parse_list(current_entry, mem, list_node_size, num_list_entries_per_node);
                    match recovered_list {
                        Some(recovered_list) => {
                            let lists_map = lists_map.insert(
                                current_entry.key(),
                                recovered_list
                            );
                            Self::parse_each_list(metadata_entries, mem, lists_map, list_node_size, num_list_entries_per_node)
                        }
                        None => None
                    }
                } else {
                    // if this entry is invalid, just continue recursing through the list
                    Self::parse_each_list(metadata_entries, mem, lists_map, list_node_size, num_list_entries_per_node)
                }
            }
        }

        pub open spec fn parse_list(
            entry: MetadataTableViewEntry<K>, 
            mem: Seq<u8>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        ) -> Option<Seq<DurableEntry<DurableListElementView<L>>>>
        {
            let head_node_index = entry.list_head_index();
            let list_len = entry.len();
            let new_list = Seq::empty();
            Self::parse_list_helper(head_node_index, list_len as int, new_list, mem, list_node_size, num_list_entries_per_node)
        }

        pub open spec fn parse_list_helper(
            cur_node_index: u64,
            list_len_remaining: int,
            current_list: Seq<DurableEntry<DurableListElementView<L>>>,
            mem: Seq<u8>,
            list_node_size: u64,
            num_list_entries_per_node: u32,
        ) -> Option<Seq<DurableEntry<DurableListElementView<L>>>>
            decreases
                list_len_remaining
        {
            if num_list_entries_per_node <= 0 {
                None 
            } else {
                // first base case: if there are no more list elements remaining, return the current list]
                // this may happen if we have allocated a node but not added any elements to it
                // for some reason, Verus can't prove termination unless this is <= rather than ==
                if list_len_remaining <= 0 {
                    Some(current_list)
                } else {
                    // 1. parse the current node
                    let result = parse_list_node::<L>(cur_node_index as int, mem, list_node_size, num_list_entries_per_node);
                    match result {
                        Some((next_node_index, current_node_element_bytes)) => {
                            // 2. add list elements to current list 
                            let elements_to_keep = if num_list_entries_per_node < list_len_remaining {
                                num_list_entries_per_node as nat
                            } else {
                                list_len_remaining as nat
                            };
                            let new_remaining = list_len_remaining - elements_to_keep;

                            // We still don't check CRCs yet because we have not yet replayed the log, so some may not be correct
                            // TODO: actually we could check CRCs now because we have replayed the log by this point
                            let parsed_elements = Seq::new(
                                elements_to_keep,
                                |i: int| {
                                    let bytes = current_node_element_bytes[i];
                                    let crc_bytes = bytes.subrange(RELATIVE_POS_OF_LIST_ELEMENT_CRC as int, RELATIVE_POS_OF_LIST_ELEMENT_CRC + 8);
                                    let list_element_bytes = bytes.subrange(RELATIVE_POS_OF_LIST_ELEMENT as int, RELATIVE_POS_OF_LIST_ELEMENT + L::spec_size_of());
                                    DurableEntry::Valid(
                                        DurableListElementView::new(
                                            u64::spec_from_bytes(crc_bytes),
                                            L::spec_from_bytes(list_element_bytes)
                                        )
                                    )
                                }
                            );

                            let current_list = current_list + parsed_elements;

                            // 3. go to next node if it exists
                            // second base case: the current node's next pointer points to itself
                            if next_node_index == cur_node_index {
                                // if list_len_remaining isn't 0 here, something is wrong -- we've reached
                                // the end of our list nodes, but haven't seen enough elements yet
                                if new_remaining != 0 {
                                    None
                                } else {
                                    Some(current_list)
                                }
                            } else {
                                Self::parse_list_helper(next_node_index, new_remaining, current_list, mem, list_node_size, num_list_entries_per_node)
                            }
                        }
                        None => None
                    }   
                }
            }   
        }

        pub exec fn get_elements_per_node(&self) -> u64 {
            self.elements_per_node
        }

        pub proof fn lemma_list_is_empty_at_setup<PM>(
            subregion: &WritablePersistentMemorySubregion,
            pm_region: &PM,
            op_log: AbstractOpLogState,
            num_keys: u64,
            node_size: u64,
            list_entries_per_node: u32,
            num_list_nodes: u64,
            metadata_table_view: MetadataTableView<K>
        ) 
            where 
                PM: PersistentMemoryRegion,
            requires
                subregion.inv(pm_region),
                forall |addr: int| #[trigger] subregion.is_writable_absolute_addr_fn()(addr),
                subregion.view(pm_region).no_outstanding_writes(),
                // op_log == AbstractOpLogState::initialize(),
            ensures 
                true
                // Self::recover(subregion.view(pm_region).flush().committed(), node_size, list_entries_per_node,
                //     op_log, metadata_table_view).unwrap() == DurableListView::<K, L>::init(),
        {
            // TODO
            assume(false);
        }

        pub exec fn setup<PM>(
            pm_region: &mut PM,
            list_id: u128,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
                ({
                    let metadata_size = ListEntryMetadata::spec_size_of();
                    let key_size = K::spec_size_of();
                    let metadata_slot_size = metadata_size + u64::spec_size_of() + key_size + u64::spec_size_of();
                    let list_element_slot_size = L::spec_size_of() + u64::spec_size_of();
                    &&& metadata_slot_size <= u64::MAX
                    &&& list_element_slot_size <= u64::MAX
                    &&& ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys) <= u64::MAX
                    &&& ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size <= u64::MAX
                }),
                L::spec_size_of() + u64::spec_size_of() < u32::MAX, // size_of is u64, but we store it in a u32 here
                // TODO: just pass it in as a u32
                0 < node_size <= u32::MAX
            ensures
                pm_region.inv(),
                pm_region@.no_outstanding_writes(),
                // TODO
        {
            // TODO: we should generate an ID to write to both regions that will
            // remain constant and indicate that the two regions are associated
            // with each other to prevent mismatched metadata and list contents
            // from being used together

            // ensure that there are no outstanding writes
            pm_region.flush();


            // check that the regions the caller passed in are sufficiently large
            let region_size = pm_region.get_region_size();

            let list_element_size = L::size_of();
            let list_element_slot_size = list_element_size + traits_t::size_of::<u64>();

            // region needs to fit at least one node
            let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size as u64;
            if required_node_region_size > region_size {
                let required = required_node_region_size as usize;
                let actual = region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            let result = Self::write_setup_metadata(pm_region, num_keys, node_size);

            pm_region.flush();

            match result {
                Ok(()) => Ok(()),
                Err(e) => Err(e)
            }
        }

        pub fn start<PM, I>(
            subregion: &PersistentMemorySubregion,
            pm_region: &PM,
            main_table: &MetadataTable<K>,
            overall_metadata: OverallMetadata,
            version_metadata: VersionMetadata,
        ) -> (result: Result<Self, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
                I: PmCopy + Sized + std::fmt::Debug,
            requires
                subregion.inv(pm_region),
                pm_region@.no_outstanding_writes(),
                overall_metadata_valid::<K, I, L>(overall_metadata, version_metadata.overall_metadata_addr, overall_metadata.kvstore_id),
                Self::parse_all_lists(
                    main_table@, 
                    subregion.view(pm_region).committed(), 
                    overall_metadata.list_node_size, 
                    overall_metadata.num_list_entries_per_node
                ) is Some,
            ensures 
                // TODO: update postcondition
                match result {
                    Ok(list) => {
                        let list_view = Self::parse_all_lists(
                            main_table@, 
                            subregion.view(pm_region).committed(), 
                            overall_metadata.list_node_size, 
                            overall_metadata.num_list_entries_per_node
                        ).unwrap();
                        &&& list@ == list_view
                        &&& list.inv(subregion.view(pm_region), main_table@, overall_metadata)
                    }
                    Err(KvError::CRCMismatch) => !pm_region.constants().impervious_to_corruption,
                    Err(KvError::LogErr { log_err }) => true, // TODO: better handling for this and PmemErr
                    Err(KvError::PmemErr { pmem_err }) => true,
                    Err(KvError::InternalError) => true,
                    Err(_) => true // TODO
                }
        
        {
            assume(false);
            let list = Self {
                list_node_region_free_list: Vec::new(),
                node_size: overall_metadata.list_node_size,
                elements_per_node: overall_metadata.num_list_entries_per_node as u64,
                num_nodes: overall_metadata.num_list_nodes,
                state: Ghost(DurableListView::init())
            };
            Ok(list)
        }

        pub exec fn abort_transaction(
            &mut self, 
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(main_table_view): Ghost<MetadataTableView<K>>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
        )
            requires
                pm.no_outstanding_writes(),
                // old(self).inv(pm, main_table_view, overall_metadata)
            ensures 
                self.inv(pm, main_table_view, overall_metadata),
                self@ == old(self)@,
        {
            assume(false);
        }

        pub exec fn update_ghost_state_to_current_bytes(
            &mut self,
            Ghost(pm): Ghost<PersistentMemoryRegionView>,
            Ghost(overall_metadata): Ghost<OverallMetadata>,
            Ghost(main_table_view): Ghost<MetadataTableView<K>>,
        )
            requires
                pm.no_outstanding_writes(),
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.list_area_addr as nat,
                        overall_metadata.list_area_size as nat);
                    Self::parse_all_lists(main_table_view, subregion_view.committed(), overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node) is Some
                })
            ensures 
                ({
                    let subregion_view = get_subregion_view(pm, overall_metadata.list_area_addr as nat,
                        overall_metadata.list_area_size as nat);
                    self@ == Self::parse_all_lists(main_table_view, subregion_view.committed(), overall_metadata.list_node_size, overall_metadata.num_list_entries_per_node).unwrap()
                }),
                // TODO: other fields
        {
            assume(false); // TODO @hayley
        }

        // // TODO: refactor into smaller functions
        // pub exec fn start<PM>(
        //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        //     list_id: u128,
        //     node_size: u32,
        //     // log_entries: &Vec<OpLogEntryType<L>>,
        //     Tracked(perm): Tracked<&TrustedListPermission>,
        //     Ghost(state): Ghost<DurableListView<K, L>>
        // ) -> (result: Result<Self, KvError<K>>)
        //     where
        //         PM: PersistentMemoryRegion,
        //     requires
        //         old(wrpm_region).inv(),
        //         ({
        //             let metadata_size = ListEntryMetadata::spec_size_of();
        //             let key_size = K::spec_size_of();
        //             let metadata_slot_size = metadata_size + u64::spec_size_of() + key_size + u64::spec_size_of();
        //             let list_element_slot_size = L::spec_size_of() + u64::spec_size_of();
        //             &&& metadata_slot_size <= u64::MAX
        //             &&& list_element_slot_size <= u64::MAX
        //         })
        //     ensures
        //         wrpm_region.inv()
        //         // TODO
        // {
        //     assume(false);

        //     // We assume that the caller set up the regions with `setup`, which checks that we got the
        //     // correct number of regions and that they are large enough, but we check again here
        //     // in case they didn't.
        //     let pm_region = wrpm_region.get_pm_region_ref();
        //     let region_size = pm_region.get_region_size();
        //     if region_size < ABSOLUTE_POS_OF_LIST_REGION_NODE_START {
        //         let required = ABSOLUTE_POS_OF_LIST_REGION_NODE_START as usize;
        //         let actual = region_size as usize;
        //         return Err(KvError::RegionTooSmall{required, actual});
        //     }

        //     // Read the metadata headers for both regions
        //     let list_region_metadata = Self::read_list_region_header(pm_region, list_id)?;

        //     // check that the region the caller passed in is sufficiently large
        //     let list_element_size = L::size_of();
        //     let list_element_slot_size = list_element_size + traits_t::size_of::<u64>();

        //     // region needs to fit at least one node
        //     let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size as u64;
        //     if required_node_region_size > region_size {
        //         let required = required_node_region_size as usize;
        //         let actual = region_size as usize;
        //         return Err(KvError::RegionTooSmall{required, actual});
        //     }

        //     let ghost mem = pm_region@.committed();

        //     // // recover the list region from the log entries
        //     // Self::replay_log_list(wrpm_region, list_id, log_entries, node_size, Tracked(perm), Ghost(state))?;

        //     // reborrow to satisfy the borrow checker
        //     let pm_region = wrpm_region.get_pm_region_ref();

        //     let mut list_node_region_free_list: Vec<u64> = Vec::new();
        //     // this list will store in-use nodes; all nodes not in this list go in the free list
        //     let mut list_nodes_in_use: Vec<u64> = Vec::new();
        //     // separate vector to help traverse the lists and fill in list_nodes_in_use
        //     let mut list_node_region_stack: Vec<u64> = Vec::new();

        //     // construct allocator for the list node region
        //     // we need to use two vectors for this -- one as a stack for traversal of the lists,
        //     // and one to record which nodes are in use
        //     let ghost mem1 = pm_region@.committed();
        //     while list_node_region_stack.len() != 0 {
        //         assume(false);
        //         let current_index = list_node_region_stack.pop().unwrap();
        //         list_nodes_in_use.push(current_index);

        //         // read the node, check its CRC; if it's fine, push its next
        //         // pointer onto the stack
        //         let list_node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START +
        //             current_index * node_size as u64;
        //         let ptr_addr = list_node_offset + RELATIVE_POS_OF_NEXT_POINTER;
        //         let ghost ptr_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ptr_addr as int + i);
        //         let crc_addr = list_node_offset + RELATIVE_POS_OF_LIST_NODE_CRC;
        //         let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr as int + i);
        //         let ptr_size_of = traits_t::size_of::<u64>();

        //         // The true next pointer and CRC are the deserializations of the bytes we originally wrote to these addresses.
        //         // To prove that the values we read are uncorrupted and initialized, we need to prove that they match these true values
        //         // using check_crc.
        //         let ghost true_next_pointer = u64::spec_from_bytes(mem1.subrange(ptr_addr as int, ptr_addr + u64::spec_size_of()));
        //         let ghost true_crc = u64::spec_from_bytes(mem1.subrange(crc_addr as int, crc_addr + u64::spec_size_of()));

        //         let next_pointer = pm_region.read_aligned::<u64>(ptr_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;
        //         let node_header_crc = pm_region.read_aligned::<u64>(crc_addr).map_err(|e| KvError::PmemErr { pmem_err: e })?;

        //         let ghost true_next_pointer_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem1[ptr_addrs[i]]);
        //         let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem1[crc_addrs[i]]);

        //         if !check_crc(next_pointer.as_slice(), node_header_crc.as_slice(), Ghost(mem1),
        //                 Ghost(pm_region.constants().impervious_to_corruption),
        //                 Ghost(ptr_addrs),
        //                 Ghost(crc_addrs)
        //         ) {
        //             return Err(KvError::CRCMismatch);
        //         }
  
        //         let next_pointer = *next_pointer.extract_init_val(
        //             Ghost(true_next_pointer), 
        //             Ghost(true_next_pointer_bytes),
        //             Ghost(pm_region.constants().impervious_to_corruption)
        //         );

        //         // If the CRC check passes, then the next pointer is valid.
        //         // If a node's next pointer points to itself, we've reached the end of the list;
        //         // otherwise, push the next pointer onto the stack
        //         if next_pointer != current_index {
        //             list_node_region_stack.push(next_pointer);
        //         }
        //     }

        //     // construct the list region allocator
        //     // TODO: this is pretty inefficient, but I don't think Verus currently supports
        //     // structures like HashMaps that might make it easier. it would be faster if
        //     // the in-use vector was sorted, but it may not be, and we don't have
        //     // access to Rust std::vec sort methods
        //     let mut found = false;
        //     for i in 0..list_region_metadata.num_nodes - 1 {
        //         assume(false);
        //         found = false;
        //         for j in 0..list_nodes_in_use.len() {
        //             assume(false);
        //             if list_nodes_in_use[j] == i {
        //                 found = true;
        //                 break;
        //             }
        //         }
        //         if !found {
        //             list_node_region_free_list.push(i);
        //         }
        //     }

        //     // The number of elements per node is the (node size - the size of the next ptr+crc) / list element size
        //     let elements_per_node = node_size as u64 - (traits_t::size_of::<u64>() as u64 * 2) / traits_t::size_of::<L>() as u64;

        //     Ok(Self {
        //         list_node_region_free_list,
        //         node_size,
        //         elements_per_node,
        //         num_nodes: list_region_metadata.num_nodes,
        //         state: Ghost(state) // TODO: this needs to be set up properly
        //     })
        // }

        // pub exec fn play_log_list<PM>(
        //     &mut self,
        //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        //     list_id: u128,
        //     log_entries: &Vec<OpLogEntryType<L>>,
        //     Tracked(perm): Tracked<&TrustedListPermission>,
        //     Ghost(state): Ghost<DurableListView<K, L>>
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion
        //     requires 
        //         // TODO 
        //     ensures 
        //         // TODO
        // {
        //     assume(false);

        //     for i in 0..log_entries.len() 
        //         invariant 
        //             // TODO 
        //     {
        //         assume(false);
        //         let log_entry = &log_entries[i];

        //         match log_entry {
        //             OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail, } => {
        //                 Self::apply_append_list_node_log_entry(wrpm_region, list_id, log_entry, 
        //                     self.node_size, Tracked(perm), Ghost(state))?;
        //             }
        //             OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => {
        //                 Self::apply_insert_list_element_log_entry(wrpm_region, list_id, log_entry, 
        //                     self.node_size, Tracked(perm), Ghost(state))?;
        //             }
        //             OpLogEntryType::NodeDeallocInMemory { old_head, new_head } => {
        //                 let mut current_node = Some(*old_head);
        //                 // TODO: current_node being None before we hit the new head would indicate
        //                 // some kind of more serious problem. This should be taken care of by verif
        //                 while current_node.is_some() && current_node.unwrap() != *new_head {
        //                     assume(false);
        //                     let cur = current_node.unwrap();
        //                     // Look up the next pointer
        //                     let next_ptr = self.get_next_list_node(wrpm_region.get_pm_region_ref(), cur, list_id)?;

        //                     // Deallocate the current node
        //                     if let Some(next_ptr) = next_ptr {
        //                         self.deallocate_node(next_ptr)?;
        //                     } else {
        //                         // This shouldn't happen
        //                         return Err(KvError::InternalError);
        //                     }
                            
        //                     // Use the next pointer for the next iteration
        //                     current_node = next_ptr;
        //                 }
        //             }
        //             _ => {} // all other entry types do not modify the list directly
        //         }
        //     }
        //     Ok(())
        // } 

        // exec fn replay_log_list<PM>(
        //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        //     list_id: u128,
        //     log_entries: &Vec<OpLogEntryType<L>>,
        //     node_size: u32,
        //     Tracked(perm): Tracked<&TrustedListPermission>,
        //     Ghost(state): Ghost<DurableListView<K, L>>
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion
        //     requires 
        //         // TODO 
        //     ensures 
        //         // TODO 
        // {
        //     assume(false);

        //     for i in 0..log_entries.len() 
        //         invariant 
        //             // TODO 
        //     {
        //         assume(false);
        //         let log_entry = &log_entries[i];

        //         match log_entry {
        //             OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail, } => {
        //                 Self::apply_append_list_node_log_entry(wrpm_region, list_id, log_entry, 
        //                     node_size, Tracked(perm), Ghost(state))?;
        //             }
        //             OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => {
        //                 Self::apply_insert_list_element_log_entry(wrpm_region, list_id, log_entry, 
        //                     node_size, Tracked(perm), Ghost(state))?;
        //             }
        //             _ => {} // all other entry types do not modify the list directly
        //         }
        //     }
        //     Ok(())
        // }

        // // These private apply_* exec fns are a bit janky, but they let us easily reuse the same
        // // replay code in the cases where list crash recovery and regular list log replay share
        // // behavior.
        // exec fn apply_insert_list_element_log_entry<PM>(
        //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        //     list_id: u128,
        //     log_entry: &OpLogEntryType<L>,
        //     node_size: u32,
        //     Tracked(perm): Tracked<&TrustedListPermission>,
        //     Ghost(state): Ghost<DurableListView<K, L>>
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion
        //     requires 
        //         // TODO
        //     ensures 
        //         // TODO 
        // {
        //     assume(false);
        //     match log_entry {
        //         OpLogEntryType::InsertListElement { node_offset, index_in_node, list_element } => {
        //             // to add a new list element, we copy it from the log to the correct index in its node
        //             let node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_offset * node_size as u64;
        //             let crc_addr = node_addr + RELATIVE_POS_OF_LIST_CONTENTS_AREA + index_in_node * traits_t::size_of::<L>() as u64;
        //             let list_element_addr = crc_addr + traits_t::size_of::<u64>() as u64;

        //             let list_element_crc = calculate_crc(list_element);

        //             wrpm_region.serialize_and_write(crc_addr, &list_element_crc, Tracked(perm));
        //             wrpm_region.serialize_and_write(list_element_addr, list_element, Tracked(perm));

        //             Ok(())
        //         }
        //         _ => Err(KvError::InternalError)
        //     }
        // }

        // exec fn apply_append_list_node_log_entry<PM>(
        //     wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
        //     list_id: u128,
        //     log_entry: &OpLogEntryType<L>,
        //     node_size: u32,
        //     Tracked(perm): Tracked<&TrustedListPermission>,
        //     Ghost(state): Ghost<DurableListView<K, L>>
        // ) -> (result: Result<(), KvError<K>>)
        //     where 
        //         PM: PersistentMemoryRegion
        //     requires 
        //         // TODO 
        //     ensures 
        //         // TODO 
        // {
        //     assume(false);
        //     match log_entry {
        //         OpLogEntryType::AppendListNode { metadata_index, old_tail, new_tail, } => {
        //             // Appending a new list node involves setting the old tail's next pointer/CRC. We have alread set the 
        //             // new tail's pointer and CRC, and we log the metadata update separately.
        //             let old_tail_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size as u64 * old_tail;

        //             let new_tail_crc = calculate_crc(new_tail);

        //             // the tail addr is the address of the next pointer
        //             let old_crc_addr = old_tail_addr + traits_t::size_of::<u64>() as u64;

        //             wrpm_region.serialize_and_write(old_tail_addr, new_tail, Tracked(perm));
        //             wrpm_region.serialize_and_write(old_crc_addr, &new_tail_crc, Tracked(perm));
        //             Ok(())
        //         }
        //         _ => Err(KvError::InternalError)
        //     }
        // }


        // Allocates a new list node, sets its next pointer,
        // and sets its CRC. This operation is not logged because modifications
        // to an unused list node are tentative. Returns the offset of the
        // allocated node.
        pub exec fn alloc_and_init_list_node<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            Ghost(list_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<u64, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                // TODO
            ensures
                wrpm_region.inv()
                // TODO
        {
            assume(false);

            // 1. allocate an unused node
            let new_node_idx = match self.list_node_region_free_list.pop() {
                Some(node) => node,
                None => return Err(KvError::OutOfSpace)
            };
            let new_node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * new_node_idx;

            // 2. set its next pointer. Since we only allocate nodes to append to the tail of 
            // the list, we'll set its next pointer to itself
            let next_ptr_addr = new_node_addr + RELATIVE_POS_OF_NEXT_POINTER;
            wrpm_region.serialize_and_write(next_ptr_addr, &new_node_idx, Tracked(perm));

            // 3. set its crc
            let crc_addr = new_node_addr + RELATIVE_POS_OF_LIST_NODE_CRC;
            let crc = calculate_crc(&new_node_idx);

            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));

            Ok(new_node_idx)
        }

        // Takes a node that has been allocated by `alloc_and_init_list_node` and
        // appends it to the the ULL by updating the old tail node's next pointer.
        // This involves committing updates, so the caller of this function must
        // have already logged:
        // 1. The update to the old tail node's next pointer
        // 2. The update to the tail node pointer in the list metadata
        pub exec fn append_list_node<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            list_id: u128,
            new_tail: u64,
            old_tail: u64,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                // TODO
                // the new tail should be initialized but not currently in use
            ensures
                wrpm_region.inv()
                // TODO
        {
            assume(false);

            // 1. obtain the address of the old tail node
            let old_tail_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * old_tail;

            // 2. update the old tail node's next pointer to point to the new tail
            let next_ptr_addr = old_tail_addr + RELATIVE_POS_OF_NEXT_POINTER;
            wrpm_region.serialize_and_write(next_ptr_addr, &new_tail, Tracked(perm));

            // 3. set its crc
            let crc_addr = old_tail_addr + RELATIVE_POS_OF_LIST_NODE_CRC;
            let crc = calculate_crc(&new_tail);
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));

            Ok(())
        }

        // Writes a new element to the next free slot in the tail node and increases
        // the length of the list by one.
        // Writing the new element to an empty slot is tentative, but updating the list
        // length is committing, and we do both in this function, so the caller must have
        // already logged:
        // 1. The new list element
        // 2. The list length update
        pub exec fn append_element<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            list_id: u128,
            tail_node: u64,
            idx: u64,
            list_element: &L,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                // TODO: require that the tail node has at least one free slot
                // TODO
            ensures
                wrpm_region.inv()
                // TODO
        {
            assume(false);

            // we don't check that the slot is empty before overwriting it, because 1) the caller has to prove that 
            // it's the next slot that should be written to and 2) list element slots do not have valid bits so there 
            // isn't a way to check this anyway

            let list_element_slot_size = L::size_of() + traits_t::size_of::<u64>();

            // 1. obtain the address of the tail node
            let tail_node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * tail_node;
            
            // 2. obtain the address at which the new list element will be written
            let idx_addr = tail_node_addr + (traits_t::size_of::<u64>() * 2) as u64 + list_element_slot_size as u64 * idx;
            let crc_addr = idx_addr;
            let element_addr = idx_addr + traits_t::size_of::<u64>() as u64;

            // 3. get the CRC of the new list element
            
            let crc = calculate_crc(list_element);

            // 4. write the new list element and its CRC
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            wrpm_region.serialize_and_write(element_addr, list_element, Tracked(perm));

            Ok(())
        }

        pub exec fn read_element_at_index<PM>(
            &self,
            pm_region: &PM,
            list_id: u128,
            node_offset: u64,
            index_in_node: u64
        ) -> (result: Result<Box<L>, KvError<K>>)
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);
            // TODO: should probably check that the node is valid

            let list_element_slot_size = L::size_of() + traits_t::size_of::<u64>();

            // 1. obtain the address of the target node
            let node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * node_offset;

            // 2. obtain the address of the element to read within the node
            let index_addr = node_addr + (traits_t::size_of::<u64>() * 2) as u64 + list_element_slot_size as u64 * index_in_node;
            let crc_addr = index_addr;
            let elem_addr = crc_addr + traits_t::size_of::<u64>() as u64;

            // 3. Read the CRC and list element
            let ghost mem = pm_region@.committed();
            
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
            let ghost true_elem_bytes = extract_bytes(mem, elem_addr as nat, L::spec_size_of());
            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost true_elem = L::spec_from_bytes(true_elem_bytes);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + i);
            let ghost elem_addrs = Seq::new(L::spec_size_of() as nat, |i: int| elem_addr + i);

            let crc = match pm_region.read_aligned::<u64>(crc_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let list_elem = match pm_region.read_aligned::<L>(elem_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };

            // 4. Check for corruption
            if !check_crc(list_elem.as_slice(), crc.as_slice(), Ghost(mem), 
                Ghost(pm_region.constants().impervious_to_corruption), Ghost(elem_addrs), Ghost(crc_addrs))
            {
                return Err(KvError::CRCMismatch);
            }

            // 5. Extract and return the uncorrupted list element
            let list_elem = list_elem.extract_init_val(Ghost(true_elem));
            Ok(list_elem)
        }

        // Deallocates the node at the given index by adding it back into the free list.
        // TODO: either the caller needs to prove that this node is actually free (i.e. not reachable from 
        // a valid head node), or we need to check it here
        // This is called as part of the `trim_list` operation, which only modifies durable state in the
        // metadata table. 
        pub exec fn deallocate_node(
            &mut self,
            idx: u64,
        ) -> (result: Result<(), KvError<K>>)
            // TODO: pre and postconditions on self
        {
            assume(false);
            if idx >= self.num_nodes {
                return Err(KvError::IndexOutOfRange);
            }
            self.list_node_region_free_list.push(idx);
            Ok(())
        }

        // TODO: maybe change PmCopy to return a u32 as the serialized len; can always cast up if necessary
        pub fn write_setup_metadata<PM>(
            pm_region: &mut PM,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
                old(pm_region)@.no_outstanding_writes(),
                L::spec_size_of() + u64::spec_size_of() < u32::MAX, // size_of is u64, but we store it in a u32 here
                // the second region is large enough for at least one node
                old(pm_region)@.len() >= ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size,
                0 < node_size <= u32::MAX,
            ensures
                pm_region.inv(),
                // TODO
        {
            assume(false);
            // Handle list node region
            // Initialize list region header and compute its CRC
            let region_size = pm_region.get_region_size();
            let num_nodes = (region_size - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / node_size as u64;
            let list_node_region_header = ListRegionHeader {
                num_nodes,
                length: region_size,
                version_number: DURABLE_LIST_REGION_VERSION_NUMBER,
                _padding0: 0,
                program_guid: DURABLE_LIST_REGION_PROGRAM_GUID
            };
            let list_node_region_header_crc = calculate_crc(&list_node_region_header);

            pm_region.serialize_and_write(ABSOLUTE_POS_OF_LIST_REGION_HEADER, &list_node_region_header);
            pm_region.serialize_and_write(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC, &list_node_region_header_crc);

            // we don't need to do any further setup here; we only count nodes as in-use if they are
            // reachable within a list, so its fine if they contain garbage while theyre not in use

            return Ok(());
        }

        fn read_list_region_header<PM>(pm_region: &PM, list_id: u128) -> (result: Result<Box<ListRegionHeader>, KvError<K>>)
            where
                PM: PersistentMemoryRegion,
            requires
                pm_region.inv(),
            ensures
                match result {
                    Ok(output_header) => {
                        true
                        // TODO
                    }
                    Err(_) => true // TODO
                }
        {
            assume(false);

            let ghost mem = pm_region@.committed();

            let ghost true_region_header = ListRegionHeader::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER + ListRegionHeader::spec_size_of()));
            let ghost true_crc = u64::spec_from_bytes(mem.subrange(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC as int, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC + u64::spec_size_of()));

            // Read the list region header and its CRC and check for corruption
            let region_header = pm_region.read_aligned::<ListRegionHeader>(ABSOLUTE_POS_OF_LIST_REGION_HEADER).map_err(|e| KvError::PmemErr { pmem_err: e })?;
            let region_header_crc = pm_region.read_aligned::<u64>(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC).map_err(|e| KvError::PmemErr { pmem_err: e })?;

            let ghost header_addrs = Seq::new(ListRegionHeader::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_LIST_REGION_HEADER as int + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC as int + i);

            let ghost true_header_bytes = Seq::new(ListRegionHeader::spec_size_of() as nat, |i: int| mem[header_addrs[i]]);
            let ghost true_crc_bytes = Seq::new(u64::spec_size_of() as nat, |i: int| mem[crc_addrs[i]]);

            if !check_crc(region_header.as_slice(), region_header_crc.as_slice(), Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs),
                    Ghost(crc_addrs))
            {
                return Err(KvError::CRCMismatch);
            }

            let region_header = region_header.extract_init_val(Ghost(true_region_header));

            if {
                ||| region_header.version_number != DURABLE_LIST_REGION_VERSION_NUMBER
                ||| region_header.program_guid != DURABLE_LIST_REGION_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListRegionMetadata);
            }

            Ok(region_header)
        }

        pub exec fn get_next_list_node<PM>(
            &self, 
            pm_region: &PM, 
            node_index: u64, 
            list_id: u128
        ) -> Result<Option<u64>, KvError<K>>
            where 
                PM: PersistentMemoryRegion,
            requires 
                // TODO 
            ensures 
                // TODO 
        {
            assume(false);

            // 1. Read the header of the provided node
            let list_element_slot_size = (L::size_of() + traits_t::size_of::<u64>()) as u64;
            let next_ptr_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * node_index;
            let crc_addr = next_ptr_addr + traits_t::size_of::<u64>() as u64;

            let ghost mem = pm_region@.committed();

            let ghost true_next_ptr_bytes = extract_bytes(mem, next_ptr_addr as nat, u64::spec_size_of());
            let ghost true_crc_bytes = extract_bytes(mem, crc_addr as nat, u64::spec_size_of());
            let ghost true_next_ptr = u64::spec_from_bytes(true_next_ptr_bytes);
            let ghost true_crc = u64::spec_from_bytes(true_crc_bytes);
            let ghost next_ptr_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| next_ptr_addr + i);
            let ghost crc_addrs = Seq::new(u64::spec_size_of() as nat, |i: int| crc_addr + i);

            let next_ptr = match pm_region.read_aligned::<u64>(next_ptr_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };
            let crc = match pm_region.read_aligned::<u64>(crc_addr) {
                Ok(val) => val,
                Err(e) => return Err(KvError::PmemErr { pmem_err: e })
            };

            if !check_crc(next_ptr.as_slice(), crc.as_slice(), Ghost(mem), 
                Ghost(pm_region.constants().impervious_to_corruption), Ghost(next_ptr_addrs), Ghost(crc_addrs))
            {
                return Err(KvError::CRCMismatch);
            }
            let next_ptr = *next_ptr.extract_init_val(Ghost(true_next_ptr));

            // 2. If the node's next pointer does not point to itself, return it; otherwise return None
            if next_ptr == node_index {
                Ok(None)
            } else {
                Ok(Some(next_ptr))
            }

        }
    }
}
