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
use super::itemsetup_v::*;
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
    phantom_pm: Ghost<core::marker::PhantomData<PM>>,
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
        local_recover::<I>(s, addrs, sm)
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        local_spec_space_needed_for_setup::<I>(ps, min_start)
    }

    pub exec fn space_needed_for_setup(ps: &SetupParameters, min_start: &OverflowingU64) -> (result: OverflowingU64)
        requires
            ps.valid(),
        ensures
            result@ == Self::spec_space_needed_for_setup(*ps, min_start@),
    {
        local_space_needed_for_setup::<I>(ps, min_start)
    }

    pub exec fn setup<K>(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<ItemTableStaticMetadata, KvError<K>>)
        where
            K: std::fmt::Debug,
        requires
            old(pm).inv(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, Set::<u64>::empty(), sm) == Some(ItemTableSnapshot::<I>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int,
                                                 sm.table.end as int)
                    &&& sm.valid()
                    &&& sm.consistent_with_type::<I>()
                    &&& min_start <= sm.table.start <= sm.table.end <= max_end
                    &&& sm.table.end - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat)
                    &&& sm.table.num_rows == ps.num_keys
                },
                Err(KvError::OutOfSpace) =>
                    max_end - min_start < Self::spec_space_needed_for_setup(*ps, min_start as nat),
                _ => false,
            },
    {
        local_setup::<PM, I, K>(pm, ps, min_start, max_end)
    }

    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        addrs: Set<u64>,
        sm: ItemTableStaticMetadata,
    )
        requires
            sm.valid(),
            sm.consistent_with_type::<I>(),
            sm.table.end <= s1.len(),
            seqs_match_in_range(s1, s2, sm.table.start as int, sm.table.end as int),
            Self::recover(s1, addrs, sm) is Some,
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        lemma_local_recover_depends_only_on_item_area::<I>(s1, s2, addrs, sm);
    }

}

}
