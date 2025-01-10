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
use itemrecover_v::*;
use std::collections::HashSet;
use std::hash::Hash;
use super::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

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
            Self::recover(journal@.read_state, item_addrs@, *sm) is Some,
        ensures
            match result {
                Ok(items) => {
                    let recovered_state = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
                    &&& items.valid(journal@, *sm)
                    &&& items@.durable == recovered_state
                    &&& items@.tentative == recovered_state
                },
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

