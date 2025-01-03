#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::keyrecover_v::*;
use super::super::kvshared_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableSnapshot<K>
{
    pub m: Map<K, (u64, u64)>,
}

impl<K> KeyTableSnapshot<K>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<K, (u64, u64)>::empty() }
    }

    pub open spec fn values(self) -> Set<(u64, u64)>
    {
        self.m.values()
    }

    pub open spec fn item_addrs(self) -> Set<u64>
    {
        self.values().map(|v: (u64, u64)| v.0)
    }

    pub open spec fn list_addrs(self) -> Set<u64>
    {
        self.values().map(|v: (u64, u64)| v.1)
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableView<K>
{
    pub durable: KeyTableSnapshot<K>,
    pub tentative: KeyTableSnapshot<K>,
}
    
#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    m: HashMap<K, u64>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub open spec fn recover(
        s: Seq<u8>,
        sm: KeyTableStaticMetadata,
    ) -> Option<KeyTableSnapshot<K>>
    {
        arbitrary()
    }

    pub exec fn setup(
        pm: &mut PM,
        sm: &KeyTableStaticMetadata,
    )
        ensures
            pm@.valid(),
            Self::recover(pm@.read_state, *sm) == Some(KeyTableSnapshot::<K>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        assume(false);
    }
}

}
