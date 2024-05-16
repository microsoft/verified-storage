use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::durable::durablelist::layout_v::*;
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub const NUM_DURABLE_LIST_REGIONS: u64 = 2;

    #[verifier::reject_recursive_types(K)]
    pub struct DurableList<K, L, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        _phantom: Ghost<core::marker::PhantomData<(K, L, E)>>,
        metadata_table_free_list: Vec<u64>,
        list_node_region_free_list: Vec<u64>,
        state: Ghost<DurableListView<K, L, E>>
    }

    impl<K, L, E> DurableList<K, L, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        pub closed spec fn view(self) -> DurableListView<K, L, E>
        {
            self.state@
        }

        // TODO
        closed spec fn inv(self) -> bool;

        pub closed spec fn recover(
            mems: Seq<Seq<u8>>,
            node_size: u64,
            op_log: Seq<OpLogEntryType>,
            list_entry_map: Map<OpLogEntryType, L>,
            kvstore_id: u128,
        ) -> Option<DurableListView<K, L, E>>
        {
            // the durable list uses two regions
            if mems.len() != 2 {
                None
            } else {
                let metadata_table_mem = mems[0];
                let list_node_region_mem = mems[1];
                if metadata_table_mem.len() < ABSOLUTE_POS_OF_METADATA_TABLE {
                    // Invalid if the metadata table sequence is not large enough
                    // to store the metadata header. It actually needs to be big
                    // enough to store an entry for every key, but we don't know
                    // the number of keys yet.
                    None
                } else {
                    // the metadata header is immutable, so we can check that is valid before doing 
                    // any log replay
                    let metadata_header_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_METADATA_HEADER as int,
                        ABSOLUTE_POS_OF_METADATA_HEADER + LENGTH_OF_METADATA_HEADER
                    );
                    let crc_bytes = metadata_table_mem.subrange(
                        ABSOLUTE_POS_OF_HEADER_CRC as int,
                        ABSOLUTE_POS_OF_HEADER_CRC + CRC_SIZE
                    );
                    let metadata_header = GlobalListMetadata::spec_deserialize(metadata_header_bytes);
                    let crc = u64::spec_deserialize(crc_bytes);
                    if crc != metadata_header.spec_crc() {
                        // The list is invalid if the stored CRC does not match the contents
                        // of the metadata header
                        None
                    } else {
                        // replay the log on the metadata table and the list region, then parse them into a list view
                        let metadata_table_mem = Self::replay_log_metadata_table(metadata_table_mem, op_log);
                        let list_nodes_mem = Self::replay_log_list_nodes(list_node_region_mem, node_size, op_log, list_entry_map);

                        // // parse the item table into a mapping index->entry so that we can use it to 
                        // // construct each list.
                        // // TODO: IGNORE INVALID ENTRIES
                        let metadata_table = parse_metadata_table(metadata_header, metadata_table_mem);
                        match metadata_table {
                            Some(metadata_table) => Self::parse_all_lists(metadata_header, metadata_table, list_node_region_mem),
                            None => None
                        }
                    }
                }
            }
        }

        closed spec fn replay_log_metadata_table(mem: Seq<u8>, op_log: Seq<OpLogEntryType>) -> Seq<u8>
            decreases op_log.len()
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_metadata_table_mem(mem, current_op);
                Self::replay_log_metadata_table(mem, op_log)
            }
        }

        // metadata table-related log entries store the CRC that the entry *will* have when all updates are written to it.
        // this ensures that we end up with the correct CRC even if updates to this entry were interrupted by a crash or 
        // if corruption has occurred. So, we don't check CRCs here, we just overwrite the current CRC with the new one and 
        // update relevant fields.
        // TODO: refactor the mapping closures
        closed spec fn apply_log_op_to_metadata_table_mem(mem: Seq<u8>, op: OpLogEntryType) -> Seq<u8>
        {
            let table_entry_slot_size = LENGTH_OF_ENTRY_METADATA_MINUS_KEY + CRC_SIZE + CDB_SIZE + K::spec_serialized_len();
            match op {
                OpLogEntryType::AppendListNode{list_metadata_index, old_tail, new_tail, metadata_crc} => {
                    // updates the tail field and the entry's CRC. We don't use the old tail value here -- that is only used
                    // when updating list nodes
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let tail_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_TAIL;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let new_tail_bytes = spec_u64_to_le_bytes(new_tail);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if tail_addr <= pos < tail_addr + 8 {
                            new_tail_bytes[pos - tail_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::UpdateListLen{list_metadata_index, new_length, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let len_bytes = spec_u64_to_le_bytes(new_length);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                } 
                OpLogEntryType::TrimList{list_metadata_index, new_head_node, new_list_len, new_list_start_index, metadata_crc} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let head_addr = entry_offset +  RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
                    let len_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let start_index_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;
                    let crc_bytes = spec_u64_to_le_bytes(metadata_crc);
                    let head_bytes = spec_u64_to_le_bytes(new_head_node);
                    let len_bytes = spec_u64_to_le_bytes(new_list_len);
                    let start_bytes = spec_u64_to_le_bytes(new_list_start_index);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if head_addr <= pos < head_addr + 8 {
                            head_bytes[pos - head_addr]
                        } else if len_addr <= pos < len_addr + 8 {
                            len_bytes[pos - len_addr]
                        } else if start_index_addr <= pos < start_index_addr + 8 {
                            start_bytes[pos - start_index_addr]
                        } else {
                            pre_byte 
                        }
                    });
                    mem
                }
                OpLogEntryType::CreateListTableEntry{list_metadata_index, head} => {
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    // construct a ghost entry with the values that the new entry will have so that we can obtain a CRC 
                    let entry = ListEntryMetadata::new(head, head, 0, 0);
                    let entry_crc = entry.spec_crc();
                    let crc_bytes = spec_u64_to_le_bytes(entry_crc);
                    let crc_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                    let head_addr = entry_offset +  RELATIVE_POS_OF_ENTRY_METADATA_HEAD;
                    let head_bytes = spec_u64_to_le_bytes(entry.spec_head());
                    // This op also implies that we need to set the tail, start index, length, and valid bytes
                    let valid_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let valid_bytes = spec_u64_to_le_bytes(CDB_TRUE);
                    let length_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_LENGTH;
                    let length_bytes = spec_u64_to_le_bytes(entry.spec_len());
                    let tail_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_TAIL;
                    let tail_bytes = spec_u64_to_le_bytes(entry.spec_tail()); // the head and tail are the same node in a new list
                    let start_index_addr = entry_offset + RELATIVE_POS_OF_ENTRY_METADATA_FIRST_OFFSET;
                    let start_bytes = spec_u64_to_le_bytes(0u64);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if head_addr <= pos < head_addr + 8 {
                            head_bytes[pos - head_addr]
                        } else if tail_addr <= pos < tail_addr + 8 {
                            tail_bytes[pos - tail_addr]
                        } else if length_addr <= pos < length_addr + 8{
                            length_bytes[pos - length_addr]
                        } else if start_index_addr <= pos < start_index_addr + 8 {
                            start_bytes[pos - start_index_addr]
                        } else if valid_addr <= pos < valid_addr + 8 {
                            valid_bytes[pos - valid_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::DeleteListTableEntry{list_metadata_index} => {
                    // In this case, we just have to flip the entry's CDB. We don't clear any other fields
                    let entry_offset = ABSOLUTE_POS_OF_METADATA_TABLE + list_metadata_index * table_entry_slot_size;
                    let cdb_addr = entry_offset + RELATIVE_POS_OF_VALID_CDB;
                    let cdb_bytes = spec_u64_to_le_bytes(CDB_FALSE);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if cdb_addr <= pos < cdb_addr + 8 {
                            cdb_bytes[pos - cdb_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other ops do not modify the metadata table
            }
        }

        closed spec fn replay_log_list_nodes(
            mem: Seq<u8>, 
            node_size: u64, 
            op_log: Seq<OpLogEntryType>, 
            list_entry_map: Map<OpLogEntryType, L>
        ) -> Seq<u8>
            decreases op_log.len() 
        {
            if op_log.len() == 0 {
                mem 
            } else {
                let current_op = op_log[0];
                let op_log = op_log.drop_first();
                let mem = Self::apply_log_op_to_list_node_mem(mem, node_size, current_op, list_entry_map);
                Self::replay_log_list_nodes(mem, node_size, op_log, list_entry_map)
            }
        }

        closed spec fn apply_log_op_to_list_node_mem(
            mem: Seq<u8>, 
            node_size: u64, 
            op: OpLogEntryType, 
            list_entry_map: Map<OpLogEntryType, L>
        ) -> Seq<u8>
        {
            match op {
                OpLogEntryType::AppendListNode{list_metadata_index, old_tail, new_tail, metadata_crc} => {
                    // To append a node, we set both the old tail and new tail's next pointers to the new tail,
                    // plus update both of their CRCs. The `metadata_crc` field in the enum is used when updating
                    // the metadata table; we just use the CRC of the new tail index here.
                    let old_tail_node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + old_tail * node_size;
                    let old_tail_next_pointer_addr = old_tail_node_offset + RELATIVE_POS_OF_NEXT_POINTER;
                    let old_tail_crc_addr = old_tail_node_offset + RELATIVE_POS_OF_LIST_NODE_CRC;
                    let new_tail_node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + new_tail * node_size;
                    let new_tail_next_pointer_addr = new_tail_node_offset + RELATIVE_POS_OF_NEXT_POINTER;
                    let new_tail_crc_addr = new_tail_node_offset + RELATIVE_POS_OF_LIST_NODE_CRC;
                    let new_tail_crc = new_tail.spec_crc();
                    let new_tail_bytes = spec_u64_to_le_bytes(new_tail);
                    let crc_bytes = spec_u64_to_le_bytes(new_tail_crc);
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if old_tail_next_pointer_addr <= pos < old_tail_next_pointer_addr + 8 {
                            new_tail_bytes[pos - old_tail_next_pointer_addr]
                        } else if old_tail_crc_addr <= pos < old_tail_crc_addr + 8 {
                            crc_bytes[pos - old_tail_crc_addr]
                        } else if new_tail_next_pointer_addr <= pos < new_tail_next_pointer_addr + 8 {
                            new_tail_bytes[pos - new_tail_next_pointer_addr]
                        } else if new_tail_crc_addr <= pos < new_tail_crc_addr + 8 {
                            crc_bytes[pos - new_tail_crc_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                OpLogEntryType::InsertListElement{node_offset, index_in_node} => {
                    let node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_offset * node_size;
                    let crc_addr = node_addr + RELATIVE_POS_OF_LIST_NODE_CRC;
                    let list_element_addr = node_addr + RELATIVE_POS_OF_LIST_CONTENTS_AREA;
                    let list_element = list_entry_map[op];
                    let crc = list_element.spec_crc();
                    let list_element_bytes = list_element.spec_serialize();
                    let crc_bytes = crc.spec_serialize();
                    let mem = mem.map(|pos: int, pre_byte: u8| {
                        if crc_addr <= pos < crc_addr + 8 {
                            crc_bytes[pos - crc_addr]
                        } else if list_element_addr <= pos < list_element_addr + L::spec_serialized_len() {
                            list_element_bytes[pos - list_element_addr]
                        } else {
                            pre_byte
                        }
                    });
                    mem
                }
                _ => mem // all other ops do not modify the list node region
            }
        }

        closed spec fn parse_all_lists(
            metadata_header: GlobalListMetadata, 
            metadata_table: Seq<DurableItemTableViewEntry<ListEntryMetadata, K>>,
            mem: Seq<u8>,
        ) -> Option<DurableListView<K, L, E>> 
        {
            let lists_map = Map::empty();
            let result = Self::parse_each_list(metadata_header, metadata_table, mem, lists_map);
            match result {
                Some(result) => Some(DurableListView::new(result)),
                None => None
            }
        }

        // Note that here, `metadata_entries` does not represent the metadata table exactly -- it's just 
        // used to help recurse over each metadata entry.
        closed spec fn parse_each_list(
            metadata_header: GlobalListMetadata,
            metadata_entries: Seq<DurableItemTableViewEntry<ListEntryMetadata, K>>,
            mem: Seq<u8>,
            lists_map: Map<K, Seq<DurableListElementView<L>>>,
        ) -> Option<Map<K, Seq<DurableListElementView<L>>>>
            decreases
                metadata_entries.len()
        {
            if metadata_entries.len() == 0 {
                Some(lists_map)
            } else {
                let current_entry = metadata_entries[0];
                let metadata_entries = metadata_entries.drop_first();
                // Unlike in the item table, we will apply log entries later; we need to build the lists 
                // first so that log entries can be applied to the table and the list in the correct order
                let recovered_list = Self::parse_list(metadata_header, current_entry.get_item(), mem);
                match recovered_list {
                    Some(recovered_list) => {
                        let lists_map = lists_map.insert(
                            current_entry.get_key(), 
                            recovered_list
                        );
                        Self::parse_each_list(metadata_header, metadata_entries, mem, lists_map)
                    }
                    None => None
                }
            }
        }

        closed spec fn parse_list(
            metadata_header: GlobalListMetadata, 
            entry: ListEntryMetadata, 
            mem: Seq<u8>
        ) -> Option<Seq<DurableListElementView<L>>>
        {
            let head_node_index = entry.spec_head();
            let list_len = entry.spec_len();
            let new_list = Seq::empty();
            Self::parse_list_helper(metadata_header, head_node_index, 
                list_len as int, new_list, mem)
        }

        closed spec fn parse_list_helper(
            metadata_header: GlobalListMetadata,
            cur_node_index: u64,
            list_len_remaining: int,
            current_list: Seq<DurableListElementView<L>>,
            mem: Seq<u8>
        ) -> Option<Seq<DurableListElementView<L>>>
            decreases
                list_len_remaining
        {
            let elements_per_node = (metadata_header.node_size - RELATIVE_POS_OF_LIST_ELEMENT) / metadata_header.element_size as int;
            if elements_per_node <= 0 {
                None 
            } else {
                // first base case: if there are no more list elements remaining, return the current list]
                // this may happen if we have allocated a node but not added any elements to it
                // for some reason, Verus can't prove termination unless this is <= rather than ==
                if list_len_remaining <= 0 {
                    Some(current_list)
                } else {
                    // 1. parse the current node
                    let result = parse_list_node::<L>(cur_node_index as int, metadata_header, mem);
                    match result {
                        Some((next_node_index, current_node_element_bytes)) => {
                            // 2. add list elements to current list 
                            let elements_to_keep = if elements_per_node < list_len_remaining {
                                elements_per_node as nat
                            } else {
                                list_len_remaining as nat
                            };
                            let new_remaining = list_len_remaining - elements_to_keep;

                            // We still don't check CRCs yet because we have not yet replayed the log, so some may not be correct
                            let parsed_elements = Seq::new(
                                elements_to_keep,
                                |i: int| {
                                    let bytes = current_node_element_bytes[i];
                                    let crc_bytes = bytes.subrange(RELATIVE_POS_OF_LIST_ELEMENT_CRC as int, RELATIVE_POS_OF_LIST_ELEMENT_CRC + 8);
                                    let list_element_bytes = bytes.subrange(RELATIVE_POS_OF_LIST_ELEMENT as int, RELATIVE_POS_OF_LIST_ELEMENT + L::spec_serialized_len());
                                    DurableListElementView::new(
                                        u64::spec_deserialize(crc_bytes),
                                        L::spec_deserialize(list_element_bytes)
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
                                Self::parse_list_helper(metadata_header, next_node_index, new_remaining, current_list, mem)
                            }
                        }
                        None => None
                    }   
                }
            }   
        }

        pub exec fn setup<PM>(
            pm_regions: &mut PM,
            list_id: u128,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(pm_regions).inv(),
                old(pm_regions)@.len() == NUM_DURABLE_LIST_REGIONS,
                ({
                    let metadata_size = ListEntryMetadata::spec_serialized_len();
                    let key_size = K::spec_serialized_len();
                    let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                    let list_element_slot_size = L::spec_serialized_len() + CRC_SIZE;
                    &&& metadata_slot_size <= u64::MAX
                    &&& list_element_slot_size <= u64::MAX
                    &&& ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys) <= u64::MAX
                    &&& ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size <= u64::MAX
                }),
                L::spec_serialized_len() + CRC_SIZE < u32::MAX, // serialized_len is u64, but we store it in a u32 here
                // TODO: just pass it in as a u32
                node_size < u32::MAX
            ensures
                pm_regions.inv(),
                pm_regions@.no_outstanding_writes(),
                // TODO
        {
            // TODO: we should generate an ID to write to both regions that will
            // remain constant and indicate that the two regions are associated
            // with each other to prevent mismatched metadata and list contents
            // from being used together

            // ensure that there are no outstanding writes
            pm_regions.flush();

            // check that the caller passed in two regions
            // one for the metadata table and one for the node region
            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 2 {
                return Err(KvError::TooFewRegions{ required: 2, actual: num_regions });
            } else if num_regions > 2 {
                return Err(KvError::TooManyRegions{ required: 2, actual: num_regions });
            }

            // check that the regions the caller passed in are sufficiently large
            let table_region_size = region_sizes[0];
            let node_region_size = region_sizes[1];
            let metadata_size = ListEntryMetadata::serialized_len();
            let metadata_slot_size = metadata_size + CRC_SIZE + K::serialized_len() + CDB_SIZE;

            let list_element_size = L::serialized_len();
            let list_element_slot_size = list_element_size + CRC_SIZE;

            // check that the table region is large enough -- needs at least as many slots as keys
            if ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys as u64) > table_region_size {
                let required = (ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys as u64)) as usize;
                let actual = table_region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            // check that the table region is large enough -- needs to fit at least one node
            let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size as u64;
            if required_node_region_size > node_region_size {
                let required = required_node_region_size as usize;
                let actual = node_region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            let result = Self::write_setup_metadata(pm_regions, num_keys, node_size);

            pm_regions.flush();

            match result {
                Ok(()) => Ok(()),
                Err(e) => Err(e)
            }
        }

        // TODO: refactor into smaller functions
        pub exec fn start<PM>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            Tracked(perm): Tracked<&TrustedListPermission>,
            Ghost(state): Ghost<DurableListView<K, L, E>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                ({
                    let metadata_size = ListEntryMetadata::spec_serialized_len();
                    let key_size = K::spec_serialized_len();
                    let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                    let list_element_slot_size = L::spec_serialized_len() + CRC_SIZE;
                    &&& metadata_slot_size <= u64::MAX
                    &&& list_element_slot_size <= u64::MAX
                })
            ensures
                wrpm_regions.inv()
                // TODO
        {
            // We assume that the caller set up the regions with `setup`, which checks that we got the
            // correct number of regions and that they are large enough, but we check again here
            // in case they didn't.
            let pm_regions = wrpm_regions.get_pm_regions_ref();
            let region_sizes = get_region_sizes(pm_regions);
            let num_regions = region_sizes.len();
            if num_regions < 2 {
                return Err(KvError::TooFewRegions{ required: 2, actual: num_regions });
            } else if num_regions > 2 {
                return Err(KvError::TooManyRegions{ required: 2, actual: num_regions });
            }
            // TODO: check that the regions are large enough to store metadata before we
            // attempt to read them

            // Read the metadata headers for both regions
            let list_metadata_table = Self::read_table_metadata(pm_regions, list_id)?;
            let list_region_metadata = Self::read_list_region_header(pm_regions, list_id)?;

            // check that the regions the caller passed in are sufficiently large
            let table_region_size = region_sizes[0];
            let node_region_size = region_sizes[1];
            let metadata_size = ListEntryMetadata::serialized_len();
            let metadata_slot_size = metadata_size + CRC_SIZE + K::serialized_len() + CDB_SIZE;

            let list_element_size = L::serialized_len();
            let list_element_slot_size = list_element_size + CRC_SIZE;

            // check that the table region is large enough -- needs at least as many slots as keys
            if ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * list_metadata_table.num_keys) > table_region_size {
                let required = (ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * list_metadata_table.num_keys)) as usize;
                let actual = table_region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            // check that the table region is large enough -- needs to fit at least one node
            let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + list_metadata_table.node_size as u64;
            if required_node_region_size > node_region_size {
                let required = required_node_region_size as usize;
                let actual = node_region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            let ghost mem = pm_regions@[0].committed();

            let mut metadata_table_free_list: Vec<u64> = Vec::with_capacity(list_metadata_table.num_keys as usize);
            let mut list_node_region_free_list: Vec<u64> = Vec::new();
            // this list will store in-use nodes; all nodes not in this list go in the free list
            let mut list_nodes_in_use: Vec<u64> = Vec::new();
            // separate vector to help traverse the lists and fill in list_nodes_in_use
            let mut list_node_region_stack: Vec<u64> = Vec::new();

            // construct allocator for the metadata table
            for index in 0..list_metadata_table.num_keys {
                assume(false);
                let metadata_slot_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * metadata_slot_size;
                let cdb_addr = metadata_slot_offset + RELATIVE_POS_OF_VALID_CDB;
                let val: &u64 = pm_regions.read_and_deserialize(0, metadata_slot_offset + cdb_addr);
                match check_cdb(&val, Ghost(mem),
                        Ghost(pm_regions.constants().impervious_to_corruption),
                        Ghost(cdb_addr)) {
                    Some(false) => metadata_table_free_list.push(index),
                    Some(true) => {
                        // We construct the list node region allocator and return metadata
                        // about list structures to the caller for indexing at the same time
                        // TODO: construct info to send to the volatile index once you have a better
                        // idea of what it will need
                        // TODO: move the read+check CRC logic into its own function
                        let crc_addr = metadata_slot_offset + RELATIVE_POS_OF_ENTRY_METADATA_CRC;
                        let entry_addr = metadata_slot_offset + RELATIVE_POS_OF_ENTRY_METADATA;
                        let key_addr = metadata_slot_offset + RELATIVE_POS_OF_ENTRY_KEY;
                        let entry_crc: &u64 = pm_regions.read_and_deserialize(0, crc_addr);
                        let entry: &ListEntryMetadata = pm_regions.read_and_deserialize(0, entry_addr);
                        let key: &K = pm_regions.read_and_deserialize(0, key_addr);
                        if !check_crc_two_deserialized(entry, key, entry_crc, Ghost(mem),
                                Ghost(pm_regions.constants().impervious_to_corruption),
                                Ghost(entry_addr),
                                Ghost(key_addr),
                                Ghost(crc_addr))
                        {
                            return Err(KvError::CRCMismatch);
                        } else {
                            // TODO: if the CRC check passes, add the information to the structure
                            // we return for the volatile index to use
                            list_node_region_stack.push(entry.get_head());
                        }
                    },
                    None => return Err(KvError::CRCMismatch)
                }
            }

            // construct allocator for the list node region
            // we need to use two vectors for this -- one as a stack for traversal of the lists,
            // and one to record which nodes are in use
            let ghost mem1 = pm_regions@[1].committed();
            while list_node_region_stack.len() != 0 {
                assume(false);
                let current_index = list_node_region_stack.pop().unwrap();
                list_nodes_in_use.push(current_index);

                // read the node, check its CRC; if it's fine, push its next
                // pointer onto the stack
                let list_node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START +
                    current_index * (list_metadata_table.node_size as u64);
                let ptr_addr = list_node_offset + RELATIVE_POS_OF_NEXT_POINTER;
                let crc_addr = list_node_offset + RELATIVE_POS_OF_LIST_NODE_CRC;
                let ptr_serialized_len = u64::serialized_len();
                let next_pointer: &u64 = pm_regions.read_and_deserialize(1, ptr_addr);
                let node_header_crc: &u64 = pm_regions.read_and_deserialize(1, crc_addr);
                if !check_crc_deserialized(next_pointer, node_header_crc, Ghost(mem1),
                        Ghost(pm_regions.constants().impervious_to_corruption),
                        Ghost(ptr_addr),
                        Ghost(ptr_serialized_len),
                        Ghost(crc_addr)
                ) {
                    return Err(KvError::CRCMismatch);
                }
                // If the CRC check passes, then the next pointer is valid.
                // If a node's next pointer points to itself, we've reached the end of the list;
                // otherwise, push the next pointer onto the stack
                if *next_pointer != current_index {
                    list_node_region_stack.push(*next_pointer);
                }
            }

            // construct the list region allocator
            // TODO: this is pretty inefficient, but I don't think Verus currently supports
            // structures like HashMaps that might make it easier. it would be faster if
            // the in-use vector was sorted, but it may not be, and we don't have
            // access to Rust std::vec sort methods
            let mut found = false;
            for i in 0..list_region_metadata.num_nodes {
                assume(false);
                found = false;
                for j in 0..list_nodes_in_use.len() {
                    assume(false);
                    if list_nodes_in_use[j] == i {
                        found = true;
                        break;
                    }
                }
                if !found {
                    list_node_region_free_list.push(i);
                }
            }

            Ok(Self {
                _phantom: Ghost(spec_phantom_data()),
                metadata_table_free_list,
                list_node_region_free_list,
                state: Ghost(state) // TODO: this needs to be set up properly
            })
        }

        // Allocates a new list node, sets its next pointer to NULL,
        // and sets its CRC. This operation is not logged because modifications
        // to an unused list node are tentative. Returns the offset of the
        // allocated node.
        pub exec fn alloc_and_init_list_node<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<u64, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // Takes a node that has been allocated by `alloc_and_init_list_node` and
        // appends it to the the ULL by updating the old tail node's next pointer.
        // This involves committing updates, so the caller of this function must
        // have already logged:
        // 1. The update to the old tail node's next pointer
        // 2. The update to the tail node pointer in the list metadata
        pub exec fn append_list_node<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            list_node_offset: u64,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // Writes a new element to the next free slot in the tail node and increases
        // the length of the list by one.
        // Writing the new element to an empty slot is tentative, but updaing the list
        // length is committing, and we do both in this function, so the caller must have
        // already logged:
        // 1. The new list element
        // 2. The list length update
        pub exec fn append_element<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            list_element: &L,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: require that the tail node has at least one free slot
                // TODO
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // Updates the element at the given list index in-place.
        // This is a committing update, so the caller must have already logged:
        // 1. The new list element
        pub exec fn update_element<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            index: u64,
            list_element: &L,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: require that the index is live
                // TODO
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // Trims the list by `trim_length` elements. In practice, this means updating
        // the list's metadata with a new length and potentially a new head node and
        // starting index offset.
        // This function does *not* modify the contents of any nodes; however, any nodes that
        // are removed from the list because all of their elements have been trimmed away
        // will be added back to the free list.
        // This is a committing update, so the caller must have already logged:
        // 1. The update to the head, length, and start index
        pub exec fn trim_list<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            trim_length: u64,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: require that trim length is valid w/ length of list
                // TODO
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // TODO: maybe change Serializable to return a u32 as the serialized len; can always cast up if necessary
        pub fn write_setup_metadata<PM>(
            pm_regions: &mut PM,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K,E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(pm_regions).inv(),
                old(pm_regions)@.no_outstanding_writes(),
                old(pm_regions)@.len() == 2,
                L::spec_serialized_len() + CRC_SIZE < u32::MAX, // serialized_len is u64, but we store it in a u32 here
                ({
                    // the first region is large enough to be the metadata table
                    let metadata_size = ListEntryMetadata::spec_serialized_len();
                    let metadata_slot_size = metadata_size + CRC_SIZE + K::spec_serialized_len() + CDB_SIZE;
                    old(pm_regions)@[0].len() >= ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys)
                }),
                // the second region is large enough for at least one node
                old(pm_regions)@[1].len() >= ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size,
                node_size <= u32::MAX,
            ensures
                pm_regions.inv(),
                // TODO
        {
            // 1) Handle metadata table
            // Initialize metadata table header and compute its CRC
            let element_size = L::serialized_len() + CRC_SIZE;
            let metadata_table_header = GlobalListMetadata {
                element_size: (L::serialized_len() + CRC_SIZE) as u32,
                node_size: node_size,
                num_keys: num_keys as u64,
                version_number: LIST_METADATA_VERSION_NUMBER,
                _padding: 0,
                program_guid: DURABLE_LIST_METADATA_TABLE_PROGRAM_GUID
            };
            let metadata_table_header_crc = calculate_crc(&metadata_table_header);

            assume(false);

            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_METADATA_HEADER, &metadata_table_header);
            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_HEADER_CRC, &metadata_table_header_crc);

            let metadata_header_entry_slot_size = CDB_SIZE + CRC_SIZE + LENGTH_OF_ENTRY_METADATA_MINUS_KEY + K::serialized_len();
            // invalidate all metadata table entries so that we can scan it and build the allocator
            for index in 0..num_keys
                // TODO: invariant
            {
                assume(false);
                let entry_slot_offset = ABSOLUTE_POS_OF_METADATA_TABLE + index * metadata_header_entry_slot_size;
                pm_regions.serialize_and_write(0, entry_slot_offset, &CDB_FALSE);
            }

            // 2) Handle list node region
            // Initialize list region header and compute its CRC
            let region_sizes = get_region_sizes(pm_regions);
            let num_nodes = (region_sizes[1] - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / node_size as u64;
            let list_node_region_header = ListRegionHeader {
                num_nodes,
                length: region_sizes[1],
                version_number: DURABLE_LIST_REGION_VERSION_NUMBER,
                _padding0: 0,
                program_guid: DURABLE_LIST_REGION_PROGRAM_GUID
            };
            let list_node_region_header_crc = calculate_crc(&list_node_region_header);

            pm_regions.serialize_and_write(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER, &list_node_region_header);
            pm_regions.serialize_and_write(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC, &list_node_region_header_crc);

            // we don't need to do any further setup here; we only count nodes as in-use if they are
            // reachable within a list, so its fine if they contain garbage while theyre not in use

            return Ok(());
        }

        pub fn read_table_metadata<PM>(pm_regions: &PM, list_id: u128) -> (result: Result<&GlobalListMetadata, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                pm_regions.inv(),
                // TODO
            ensures
                match result {
                    Ok(output_metadata) => {
                        let metadata_size = ListEntryMetadata::spec_serialized_len();
                        let key_size = K::spec_serialized_len();
                        let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                        &&& output_metadata.num_keys * metadata_slot_size <= u64::MAX
                        &&& ABSOLUTE_POS_OF_METADATA_TABLE + metadata_slot_size * output_metadata.num_keys  <= u64::MAX
                    }
                    Err(_) => true // TODO
                }
                // TODO
        {
            assume(false);

            let ghost mem = pm_regions@[0].committed();

            // read in the header and its CRC, check for corruption
            let metadata: &GlobalListMetadata = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_METADATA_HEADER);
            let metadata_crc = pm_regions.read_and_deserialize(0, ABSOLUTE_POS_OF_HEADER_CRC);

            if !check_crc_deserialized(metadata, metadata_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_METADATA_HEADER), Ghost(LENGTH_OF_METADATA_HEADER),
                    Ghost(ABSOLUTE_POS_OF_HEADER_CRC)) {
                return Err(KvError::CRCMismatch);
            }

            // Since we've already checked for corruption, this condition will only fail
            // if the caller tries to use an L with a different size than the one
            // the list was originally set up with
            if {
                ||| metadata.element_size != (L::serialized_len() + CRC_SIZE) as u32
                ||| metadata.version_number != LIST_METADATA_VERSION_NUMBER
                ||| metadata.program_guid != DURABLE_LIST_METADATA_TABLE_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListMetadata);
            }

            Ok(metadata)
        }

        fn read_list_region_header<PM>(pm_regions: &PM, list_id: u128) -> (result: Result<&ListRegionHeader, KvError<K,E>>)
            where
                PM: PersistentMemoryRegions
            requires
                pm_regions.inv(),
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

            let ghost mem = pm_regions@[1].committed();

            // Read the list region header and its CRC and check for corruption
            let region_header: &ListRegionHeader = pm_regions.read_and_deserialize(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER);
            let region_header_crc = pm_regions.read_and_deserialize(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC);

            if !check_crc_deserialized(region_header, region_header_crc, Ghost(mem),
                    Ghost(pm_regions.constants().impervious_to_corruption),
                    Ghost(ABSOLUTE_POS_OF_LIST_REGION_HEADER), Ghost(LENGTH_OF_LIST_REGION_HEADER),
                    Ghost(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC))
            {
                return Err(KvError::CRCMismatch);
            }

            if {
                ||| region_header.version_number != DURABLE_LIST_REGION_VERSION_NUMBER
                ||| region_header.program_guid != DURABLE_LIST_REGION_PROGRAM_GUID
            } {
                return Err(KvError::InvalidListRegionMetadata);
            }

            Ok(region_header)
        }
    }
}
