use crate::itemtable::itemtablespec_t::*;
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

        pub exec fn tentatively_write_item<PM>(
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
            ensures
                wrpm_regions.inv()
                // TODO
        {
            assume(false);
            Err(KvError::NotImplemented)
        }


    }
}
