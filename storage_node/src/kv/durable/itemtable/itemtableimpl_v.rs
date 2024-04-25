use crate::kv::durable::itemtable::itemtablespec_t::*;
use crate::kv::kvimpl_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use std::hash::Hash;
use vstd::prelude::*;

verus! {
    pub struct DurableItemTable<K, I, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        _phantom: Ghost<core::marker::PhantomData<(K, I, E)>>,
        free_list: Vec<u64>,
        state: Ghost<DurableItemTableView<I>>,
    }

    impl<K, I, E> DurableItemTable<K, I, E>
        where
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        pub closed spec fn view(self) -> DurableItemTableView<I>
        {
            self.state@
        }

        // TODO: write invariants
        closed spec fn inv(self) -> bool;

        pub exec fn setup<PM>(
            pm_regions: &mut PM,
            item_table_id: u128,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions,
            requires
                old(pm_regions).inv()
            ensures
                pm_regions.inv(),
                pm_regions@.no_outstanding_writes(),
                // TODO: write the rest of the postconditions
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        pub exec fn start<PM>(
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
            Ghost(state): Ghost<DurableItemTableView<I>>
        ) -> (result: Result<Self, KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: recovery and permissions checks
            ensures
                wrpm_regions.inv(),
                // TODO: write the rest of the postconditions
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // // this function should obtain a free entry from the free list
        // // but does NOT update a durable allocator -- that should only
        // // happen after the allocation has been logged
        // pub exec fn get_free_table_entry(
        //     item_table_id: u128,
        // ) -> (result: Result<u64, KvError<K, E>>)
        // {
        //     assume(false);
        //     Err(KvError::NotImplemented)
        // }

        // // given a table slot whose allocation has been logged, this function
        // // updates the durable allocator to reflect that the slot has been
        // // allocated
        // pub exec fn alloc_table_entry<PM>(
        //     wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
        //     item_table_id: u128,
        //     table_index: u64,
        //     Tracked(perm): Tracked<&TrustedItemTablePermission>,
        // ) -> (result: Result<u64, KvError<K, E>>)
        //     where
        //         PM: PersistentMemoryRegions
        //     requires
        //         old(wrpm_regions).inv(),
        //         // TODO: given index should be allocated but invalid
        //         // or should we check that at runtime?
        //     ensures
        //         wrpm_regions.inv()
        //         // TODO
        // {
        //     assume(false);
        //     Err(KvError::NotImplemented)
        // }

        // this function can be used to both create new items and do COW updates to existing items.
        // must always write to an invalid slot
        // this operation is NOT directly logged
        // what does this return....?????????
        pub exec fn tentatively_write_item<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            item: &I,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(u64, u64), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv()
                // TODO
                // should only be able to write to an allocated but invalid slot
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // makes a slot valid by setting its valid bit.
        // must log the operation before calling this function
        pub exec fn commit_item<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            offset: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: item update must have been logged
            ensures
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }

        // clears the valid bit for an entry. this should also
        // deallocate it
        pub exec fn invalidate_item<PM>(
            &mut self,
            wrpm_regions: &mut WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
            item_table_id: u128,
            offset: u64,
            Tracked(perm): Tracked<&TrustedItemTablePermission>,
        ) -> (result: Result<(), KvError<K, E>>)
            where
                PM: PersistentMemoryRegions
            requires
                old(wrpm_regions).inv(),
                // TODO: item invalidation must have been logged
            ensures
                wrpm_regions.inv(),
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }


    }
}
