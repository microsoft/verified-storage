use crate::kv::durable::durablelist::durablelistspec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
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
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(pm_regions).inv(),
                old(pm_regions)@.len() == NUM_DURABLE_LIST_REGIONS
            ensures
                pm_regions.inv(),
                pm_regions@.no_outstanding_writes(),
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
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
    }
}
