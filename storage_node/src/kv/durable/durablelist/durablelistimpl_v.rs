use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::durable::durablelist::layout_v::*;
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
        node_area_free_list: Vec<u64>,
        state: Ghost<DurableListView<K, L>>
    }

    impl<K, L, E> DurableList<K, L, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        pub closed spec fn view(self) -> DurableListView<K, L>
        {
            self.state@
        }

        // TODO
        closed spec fn inv(self) -> bool;

        pub exec fn setup<PM>(
            pm_regions: &mut PM,
            list_id: u128,
            num_keys: u64,
            node_size: u64,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(pm_regions).inv(),
                old(pm_regions)@.len() == NUM_DURABLE_LIST_REGIONS,
                ({
                    let metadata_size = ListEntryMetadata::spec_serialized_len();
                    let key_size = K::spec_serialized_len();
                    let metadata_slot_size = metadata_size + CRC_SIZE + key_size + VALID_BYTES_SIZE;
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
            let metadata_slot_size = metadata_size + CRC_SIZE + K::serialized_len() + VALID_BYTES_SIZE;

            let list_element_size = L::serialized_len();
            let list_element_slot_size = list_element_size + CRC_SIZE;

            // check that the table region is large enough -- needs at least as many slots as keys
            if ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys) > table_region_size {
                let required = (ABSOLUTE_POS_OF_METADATA_TABLE + (metadata_slot_size * num_keys)) as usize;
                let actual = table_region_size as usize;
                return Err(KvError::RegionTooSmall{required, actual});
            }

            // check that the table region is large enough -- needs to fit at least one node
            let required_node_region_size = ABSOLUTE_POS_OF_LIST_REGION_NODE_START + node_size;
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

        pub exec fn start<PM>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
            list_id: u128,
            Tracked(perm): Tracked<&TrustedListPermission>,
            Ghost(state): Ghost<DurableListView<K, L>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv()
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
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
            node_size: u64,
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
                    let metadata_slot_size = metadata_size + CRC_SIZE + K::spec_serialized_len() + VALID_BYTES_SIZE;
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
                node_size: node_size as u32,
                num_keys,
                version_number: LIST_METADATA_VERSION_NUMBER,
                _padding: 0,
                program_guid: DURABLE_LIST_METADATA_TABLE_PROGRAM_GUID
            };
            let metadata_table_header_crc = calculate_crc(&metadata_table_header);

            assume(false);

            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_METADATA_HEADER, &metadata_table_header);
            pm_regions.serialize_and_write(0, ABSOLUTE_POS_OF_HEADER_CRC, &metadata_table_header_crc);

            let metadata_header_entry_slot_size = VALID_BYTES_SIZE + CRC_SIZE + LENGTH_OF_ENTRY_METADATA_MINUS_KEY + K::serialized_len();
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
            let num_nodes = (region_sizes[1] - ABSOLUTE_POS_OF_LIST_REGION_NODE_START) / node_size;
            let list_node_region_header = ListRegionHeader {
                num_nodes,
                version_number: DURABLE_LIST_REGION_VERSION_NUMBER,
                program_guid: DURABLE_LIST_REGION_PROGRAM_GUID
            };
            let list_node_region_header_crc = calculate_crc(&list_node_region_header);

            pm_regions.serialize_and_write(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER, &list_node_region_header);
            pm_regions.serialize_and_write(1, ABSOLUTE_POS_OF_LIST_REGION_HEADER_CRC, &list_node_region_header_crc);

            // we don't need to do any further setup here; we only count nodes as in-use if they are
            // reachable within a list, so its fine if they contain garbage while theyre not in use

            return Ok(());
        }
    }
}
