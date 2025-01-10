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
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start(
        journal: &Journal<TrustedKvPermission, PM>,
        sm: &KeyTableStaticMetadata,
        Tracked(perm): Tracked<TrustedKvPermission>,
    ) -> (result: Result<Self, KvError<K>>)
        requires
            Self::recover(journal@.read_state, *sm) is Some,
        ensures
            match result {
                Ok(keys) => {
                    &&& keys.valid(journal@, *sm)
                    &&& keys@.durable == Self::recover(journal@.read_state, *sm).unwrap()
                    &&& keys@.tentative == Self::recover(journal@.read_state, *sm).unwrap()
                },
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

