#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::itemrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvrecover_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::ext_equal]
pub struct ItemTableSnapshot<I>
{
    pub m: Map<u64, I>,
}

impl<I> ItemTableSnapshot<I>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<u64, I>::empty() }
    }
}

#[verifier::ext_equal]
pub struct ItemTableView<I>
{
    pub durable: ItemTableSnapshot<I>,
    pub tentative: ItemTableSnapshot<I>,
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
    pub closed spec fn recover(
        s: Seq<u8>,
        addrs: Set<u64>,
        sm: ItemTableStaticMetadata,
    ) -> Option<ItemTableSnapshot<I>>
    {
        recover_items::<I>(s, addrs, sm)
    }

    pub closed spec fn space_needed_for_setup(ps: SetupParameters) -> int
    {
        arbitrary()
    }

    pub exec fn get_space_needed_for_setup(ps: &SetupParameters) -> (result: OverflowingU64)
        ensures
            result@ == Self::space_needed_for_setup(*ps),
    {
        assume(false);
        OverflowingU64::new(0)
    }

    pub exec fn setup(
        pm: &mut PM,
        sm: &ItemTableStaticMetadata,
    )
        requires
            old(pm).inv(),
            sm.valid(),
            sm.consistent_with_type::<I>(),
            sm.table.end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            Self::recover(pm@.read_state, Set::<u64>::empty(), *sm) == Some(ItemTableSnapshot::<I>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        assume(false);
    }
}

}
