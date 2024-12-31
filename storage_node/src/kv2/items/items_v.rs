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

#[verifier::ext_equal]
pub struct ItemTableSnapshot<I>
{
    pub m: Map<int, I>,
}

impl<I> ItemTableSnapshot<I>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<int, I>::empty() }
    }
}

#[verifier::ext_equal]
pub struct ItemTableView<I>
{
    pub durable: ItemTableSnapshot<I>,
    pub tentative: ItemTableSnapshot<I>,
}

impl<I> ItemTableView<I>
{
    pub open spec fn init() -> Self
    {
        Self {
            durable: ItemTableSnapshot::<I>::init(),
            tentative: ItemTableSnapshot::<I>::init(),
        }
    }
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(I)]
pub struct ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    m: HashMap<u64, I>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub open spec fn recover(
        s: Seq<u8>,
        config: KvConfiguration
    ) -> Option<ItemTableView<I>>
    {
        None
    }

    pub exec fn setup(
        pm: &mut PM,
        config: &KvConfiguration,
    )
        ensures
            pm@.valid(),
            Self::recover(pm@.read_state, *config) == Some(ItemTableView::<I>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, config.item_table_start as int,
                                       config.item_table_end as int),
    {
        assume(false);
    }
}

}
