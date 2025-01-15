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

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start<K>(
        journal: &Journal<TrustedKvPermission, PM>,
        item_addrs: &HashSet<u64>,
        sm: &ItemTableStaticMetadata,
    ) -> (result: Result<Self, KvError<K>>)
        where
            K: std::fmt::Debug,
        requires
            journal.valid(),
            journal.recover_idempotent(),
            journal@.valid(),
            journal@.journaled_addrs == Set::<int>::empty(),
            journal@.durable_state == journal@.read_state,
            journal@.read_state == journal@.commit_state,
            Self::recover(journal@.read_state, item_addrs@, *sm) is Some,
            sm.valid::<I>(),
            sm.end() <= journal@.durable_state.len(),
        ensures
            match result {
                Ok(items) => {
                    let recovered_state = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
                    &&& items.valid(journal@)
                    &&& items@.sm == *sm
                    &&& items@.durable == recovered_state
                    &&& items@.tentative == Some(recovered_state)
                    &&& recovered_state.m.dom() == item_addrs@
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

