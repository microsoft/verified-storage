#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use recover_v::*;
use std::collections::HashSet;
use std::hash::Hash;
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn start<K>(
        journal: &Journal<TrustedKvPermission, PM>,
        logical_range_gaps_policy: LogicalRangeGapsPolicy,
        list_addrs: &HashSet<u64>,
        sm: &ListTableStaticMetadata,
    ) -> (result: Result<Self, KvError<K>>)
        where
            K: std::fmt::Debug,
        requires
            Self::recover(journal@.read_state, list_addrs@, *sm) is Some,
        ensures
            match result {
                Ok(lists) => {
                    let recovered_state = Self::recover(journal@.read_state, list_addrs@, *sm).unwrap();
                    &&& lists.valid(journal@, *sm)
                    &&& lists@.sm == *sm
                    &&& lists@.logical_range_gaps_policy == logical_range_gaps_policy
                    &&& lists@.durable == recovered_state
                    &&& lists@.tentative == Some(recovered_state)
                    &&& recovered_state.m.dom() == list_addrs@
                },
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

