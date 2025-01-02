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
    pub m: Map<K, int>,
}

impl<K> KeyTableSnapshot<K>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<K, int>::empty() }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableView<K>
{
    pub durable: KeyTableSnapshot<K>,
    pub tentative: KeyTableSnapshot<K>,
}

impl<K> KeyTableView<K>
{
    pub open spec fn init() -> Self
    {
        Self {
            durable: KeyTableSnapshot::<K>::init(),
            tentative: KeyTableSnapshot::<K>::init(),
        }
    }
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
    ) -> Option<KeyTableView<K>>
    {
        arbitrary()
    }

    pub exec fn setup(
        pm: &mut PM,
        sm: &KeyTableStaticMetadata,
    )
        ensures
            pm@.valid(),
            Self::recover(pm@.read_state, *sm) == Some(KeyTableView::<K>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        assume(false);
    }
}

}
