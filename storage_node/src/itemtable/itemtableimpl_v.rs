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
    pub struct DurableItemTable<PM, K, I, E>
        where
            PM: PersistentMemoryRegions,
            K: Hash + Eq + Clone + Serializable + Sized + std::fmt::Debug,
            I: Serializable + Item<K> + Sized + std::fmt::Debug,
            E: std::fmt::Debug,
    {
        wrpm_regions: WriteRestrictedPersistentMemoryRegions<TrustedItemTablePermission, PM>,
    }
}
