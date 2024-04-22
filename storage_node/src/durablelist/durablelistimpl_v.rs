use crate::durablelist::durablelistspec_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    pub struct DurableList<PM, L, E>
        where
            PM: PersistentMemoryRegions,
            L: Serializable + std::fmt::Debug,
            E: std::fmt::Debug
    {
        wrpm_regions: WriteRestrictedPersistentMemoryRegions<TrustedListPermission, PM>,
    }

}
