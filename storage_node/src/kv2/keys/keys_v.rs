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
use super::super::kvimpl_t::*;
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

pub open spec fn key_table_recover<K>(
    s: Seq<u8>,
    config: KvConfiguration
) -> Option<KeyTableView<K>>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    None
}
    
#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTable<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    m: HashMap<K, u64>,
}

impl<K> KeyTable<K>
    where
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn setup<PM>(
        pm: &mut PM,
        config: &KvConfiguration,
    )
        where
            PM: PersistentMemoryRegion,
        ensures
            pm@.valid(),
            key_table_recover::<K>(pm@.read_state, *config) == Some(KeyTableView::<K>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, config.key_table_start as int,
                                       config.key_table_end as int),
    {
        assume(false);
    }
}

}
