use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::durable::durablelist::layout_v::*;
use crate::kv::durable::logentry_t::*;
use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::durable::metadata::layout_v::*;
use crate::kv::durable::metadata::metadataspec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::crc_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_t::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub const NUM_DURABLE_LIST_REGIONS: u64 = 1;

    #[verifier::reject_recursive_types(K)]
    pub struct DurableList<K, L, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        _phantom: Ghost<core::marker::PhantomData<(K, L, E)>>,
        list_node_region_free_list: Vec<u64>,
        node_size: u32,
        num_nodes: u64,
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
            mem: Seq<u8>,
            node_size: u64,
            op_log: Seq<OpLogEntryType<L>>,
            metadata_table_view: MetadataTableView<K>,
            kvstore_id: u128,
        ) -> Option<DurableListView<K, L, E>>
        {
            // TODO: check list node region header for validity? or do we do that later?
            let list_nodes_mem = Self::replay_log_list_nodes(mem, node_size, op_log);
            Self::parse_all_lists(metadata_table_view, mem)
        }

        closed spec fn replay_log_list_nodes(
            mem: Seq<u8>, 
            node_size: u64, 
            op_log: Seq<OpLogEntryType<L>>, 
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

        closed spec fn apply_log_op_to_list_node_mem(
            mem: Seq<u8>, 
            node_size: u64, 
            op: OpLogEntryType<L>, 
        ) -> Seq<u8>
        {
            match op {
                OpLogEntryType::AppendListNode{metadata_index, old_tail, new_tail, metadata_crc} => {
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
                OpLogEntryType::InsertListElement{node_offset, index_in_node, list_element} => {
                    let node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_offset * node_size;
                    let crc_addr = node_addr + RELATIVE_POS_OF_LIST_NODE_CRC;
                    let list_element_addr = node_addr + RELATIVE_POS_OF_LIST_CONTENTS_AREA;
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
            metadata_table: MetadataTableView<K>,
            mem: Seq<u8>,
        ) -> Option<DurableListView<K, L, E>> 
        {
            let lists_map = Map::empty();
            let result = Self::parse_each_list(metadata_table.get_metadata_header(), metadata_table.get_metadata_table(), mem, lists_map);
            match result {
                Some(result) => Some(DurableListView::new(result)),
                None => None
            }
        }

        // Note that here, `metadata_entries` does not represent the metadata table exactly -- it's just 
        // used to help recurse over each metadata entry.
        closed spec fn parse_each_list(
            metadata_header: MetadataTableHeader,
            metadata_entries: Seq<MetadataTableViewEntry<K>>,
            mem: Seq<u8>,
            lists_map: Map<K, Seq<DurableListElementView<L>>>,
        ) -> Option<Map<K, Seq<DurableListElementView<L>>>>
            decreases
                metadata_entries.len()
        {
            if metadata_entries.len() <= 0 {
                Some(lists_map)
            } else {
                let current_entry = metadata_entries[0];
                let metadata_entries = metadata_entries.drop_first();
                // // Unlike in the item table, we will apply log entries later; we need to build the lists 
                // // first so that log entries can be applied to the table and the list in the correct order
                let recovered_list = Self::parse_list(metadata_header, current_entry, mem);
                match recovered_list {
                    Some(recovered_list) => {
                        let lists_map = lists_map.insert(
                            current_entry.key(),
                            recovered_list
                        );
                        Self::parse_each_list(metadata_header, metadata_entries, mem, lists_map)
                    }
                    None => None
                }
            }
        }

        closed spec fn parse_list(
            metadata_header: MetadataTableHeader, 
            entry: MetadataTableViewEntry<K>, 
            mem: Seq<u8>
        ) -> Option<Seq<DurableListElementView<L>>>
        {
            let head_node_index = entry.list_head_index();
            let list_len = entry.len();
            let new_list = Seq::empty();
            Self::parse_list_helper(metadata_header, head_node_index, 
                list_len as int, new_list, mem)
        }

        closed spec fn parse_list_helper(
            metadata_header: MetadataTableHeader,
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
                            // TODO: actually we could check CRCs now because we have replayed the log by this point
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
            pm_region: &mut PM,
            list_id: u128,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
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

            let list_element_size = L::serialized_len();
            let list_element_slot_size = list_element_size + CRC_SIZE;

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

        // TODO: refactor into smaller functions
        pub exec fn start<PM>(
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            list_id: u128,
            node_size: u32,
            Tracked(perm): Tracked<&TrustedListPermission>,
            Ghost(state): Ghost<DurableListView<K, L, E>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                ({
                    let metadata_size = ListEntryMetadata::spec_serialized_len();
                    let key_size = K::spec_serialized_len();
                    let metadata_slot_size = metadata_size + CRC_SIZE + key_size + CDB_SIZE;
                    let list_element_slot_size = L::spec_serialized_len() + CRC_SIZE;
                    &&& metadata_slot_size <= u64::MAX
                    &&& list_element_slot_size <= u64::MAX
                })
            ensures
                wrpm_region.inv()
                // TODO
        {
            // We assume that the caller set up the regions with `setup`, which checks that we got the
            // correct number of regions and that they are large enough, but we check again here
            // in case they didn't.
            let pm_region = wrpm_region.get_pm_region_ref();
            let region_size = pm_region.get_region_size();
            if region_size < ABSOLUTE_POS_OF_LIST_REGION_NODE_START {
                let required = ABSOLUTE_POS_OF_LIST_REGION_NODE_START as usize;
                let actual = region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            // Read the metadata headers for both regions
            let list_region_metadata = Self::read_list_region_header(pm_region, list_id)?;

            // check that the region the caller passed in is sufficiently large
            let list_element_size = L::serialized_len();
            let list_element_slot_size = list_element_size + CRC_SIZE;

            // region needs to fit at least one node
            let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size as u64;
            if required_node_region_size > region_size {
                let required = required_node_region_size as usize;
                let actual = region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            let ghost mem = pm_region@.committed();

            let mut list_node_region_free_list: Vec<u64> = Vec::new();
            // this list will store in-use nodes; all nodes not in this list go in the free list
            let mut list_nodes_in_use: Vec<u64> = Vec::new();
            // separate vector to help traverse the lists and fill in list_nodes_in_use
            let mut list_node_region_stack: Vec<u64> = Vec::new();

            // construct allocator for the list node region
            // we need to use two vectors for this -- one as a stack for traversal of the lists,
            // and one to record which nodes are in use
            let ghost mem1 = pm_region@.committed();
            while list_node_region_stack.len() != 0 {
                assume(false);
                let current_index = list_node_region_stack.pop().unwrap();
                list_nodes_in_use.push(current_index);

                // read the node, check its CRC; if it's fine, push its next
                // pointer onto the stack
                let list_node_offset = ABSOLUTE_POS_OF_LIST_REGION_NODE_START +
                    current_index * node_size as u64;
                let ptr_addr = list_node_offset + RELATIVE_POS_OF_NEXT_POINTER;
                let ghost ptr_addrs = Seq::new(u64::spec_serialized_len(), |i: int| ptr_addr as int + i);
                let crc_addr = list_node_offset + RELATIVE_POS_OF_LIST_NODE_CRC;
                let ghost crc_addrs = Seq::new(CRC_SIZE as nat, |i: int| crc_addr as int + i);
                let ptr_serialized_len = u64::serialized_len();
                let next_pointer: &u64 = pm_region.read_and_deserialize(ptr_addr);
                let node_header_crc: &u64 = pm_region.read_and_deserialize(crc_addr);
                if !check_crc_deserialized2(next_pointer, node_header_crc, Ghost(mem1),
                        Ghost(pm_region.constants().impervious_to_corruption),
                        Ghost(ptr_addrs),
                        Ghost(crc_addrs)
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
                list_node_region_free_list,
                node_size: node_size,
                num_nodes: list_region_metadata.num_nodes,
                state: Ghost(state) // TODO: this needs to be set up properly
            })
        }

        // Allocates a new list node, sets its next pointer,
        // and sets its CRC. This operation is not logged because modifications
        // to an unused list node are tentative. Returns the offset of the
        // allocated node.
        pub exec fn alloc_and_init_list_node<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            Ghost(list_id): Ghost<u128>,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<u64, KvError<K, E>>)
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
        ) -> (result: Result<(), KvError<K, E>>)
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
        ) -> (result: Result<(), KvError<K, E>>)
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

            let list_element_slot_size = L::serialized_len() + CRC_SIZE;

            // 1. obtain the address of the tail node
            let tail_node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * tail_node;

            // 2. obtain the address at which the new list element will be written
            let idx_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + LENGTH_OF_LIST_NODE_HEADER + list_element_slot_size * idx;
            let element_addr = idx_addr + RELATIVE_POS_OF_LIST_ELEMENT;

            // 3. get the CRC of the new list element
            let crc_addr = idx_addr + RELATIVE_POS_OF_LIST_ELEMENT_CRC;
            let crc = calculate_crc(list_element);

            // 4. write the new list element and its CRC
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            wrpm_region.serialize_and_write(element_addr, list_element, Tracked(perm));

            Ok(())
        }

        // Updates the element at the given list index in-place.
        // This is a committing update, so the caller must have already logged:
        // 1. The new list element
        pub exec fn update_element<PM>(
            &mut self,
            wrpm_region: &mut WriteRestrictedPersistentMemoryRegion<TrustedListPermission, PM>,
            list_id: u128,
            node_idx: u64,
            element_idx: u64,
            list_element: &L,
            Tracked(perm): Tracked<&TrustedListPermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(wrpm_region).inv(),
                // TODO: require that the index is live
                // TODO
            ensures
                wrpm_region.inv()
                // TODO
        {
            assume(false);

            // The implementation of this method is pretty much the same as `append_element`, except that we specify
            // which node to modify (rather than always writing to the tail) and the proof requirements are different,
            // since updating an element is a committing update

            let list_element_slot_size = L::serialized_len() + CRC_SIZE;

            // 1. obtain the address of the tail node
            let tail_node_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + self.node_size as u64 * node_idx;

            // 2. obtain the address at which the new list element will be written
            let idx_addr = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + LENGTH_OF_LIST_NODE_HEADER + list_element_slot_size * element_idx;
            let element_addr = idx_addr + RELATIVE_POS_OF_LIST_ELEMENT;

            // 3. get the CRC of the new list element
            let crc_addr = idx_addr + RELATIVE_POS_OF_LIST_ELEMENT_CRC;
            let crc = calculate_crc(list_element);

            // 4. write the new list element and its CRC
            wrpm_region.serialize_and_write(crc_addr, &crc, Tracked(perm));
            wrpm_region.serialize_and_write(element_addr, list_element, Tracked(perm));

            Ok(())
        }

        // Deallocates the node at the given index by adding it back into the free list.
        // TODO: either the caller needs to prove that this node is actually free (i.e. not reachable from 
        // a valid head node), or we need to check it here
        // This is called as part of the `trim_list` operation, which only modifies durable state in the
        // metadata table. 
        pub exec fn deallocate_node(
            &mut self,
            idx: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            // TODO: pre and postconditions on self
        {
            assume(false);
            if idx >= self.num_nodes {
                return Err(KvError::IndexOutOfRange);
            }
            self.list_node_region_free_list.push(idx);
            Ok(())
        }

        // TODO: maybe change Serializable to return a u32 as the serialized len; can always cast up if necessary
        pub fn write_setup_metadata<PM>(
            pm_region: &mut PM,
            num_keys: u64,
            node_size: u32,
        ) -> (result: Result<(), KvError<K,E>>)
            where
                PM: PersistentMemoryRegion,
            requires
                old(pm_region).inv(),
                old(pm_region)@.no_outstanding_writes(),
                L::spec_serialized_len() + CRC_SIZE < u32::MAX, // serialized_len is u64, but we store it in a u32 here
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

        fn read_list_region_header<PM>(pm_region: &PM, list_id: u128) -> (result: Result<&ListRegionHeader, KvError<K,E>>)
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

            // Read the list region header and its CRC and check for corruption
            let region_header: &ListRegionHeader = pm_region.read_and_deserialize(ABSOLUTE_POS_OF_LIST_REGION_HEADER);
            let region_header_crc = pm_region.read_and_deserialize(ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC);

            let ghost header_addrs = Seq::new(ListRegionHeader::spec_serialized_len(), |i: int| ABSOLUTE_POS_OF_LIST_REGION_HEADER as int + i);
            let ghost crc_addrs = Seq::new(CRC_SIZE as nat, |i: int| ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC as int + i);

            if !check_crc_deserialized2(region_header, region_header_crc, Ghost(mem),
                    Ghost(pm_region.constants().impervious_to_corruption),
                    Ghost(header_addrs),
                    Ghost(crc_addrs))
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
