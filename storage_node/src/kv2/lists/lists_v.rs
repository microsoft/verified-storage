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
use std::hash::Hash;
use super::listrecover_v::*;
use crate::common::table_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::ext_equal]
pub struct ListTableSnapshot<L>
{
    pub m: Map<u64, Seq<L>>, // always maps the null address (0) to the empty sequence
}

impl<L> ListTableSnapshot<L>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<u64, Seq<L>>::empty() }
    }
}

#[verifier::ext_equal]
pub struct ListTableView<L>
{
    pub durable: ListTableSnapshot<L>,
    pub tentative: ListTableSnapshot<L>,
}

#[verifier::ext_equal]
pub struct ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    m: Map<u64, Vec<L>>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub closed spec fn recover(
        s: Seq<u8>,
        addrs: Set<u64>,
        sm: ListTableStaticMetadata,
    ) -> Option<ListTableSnapshot<L>>
    {
        recover_lists::<L>(s, addrs, sm)
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
        sm: &ListTableStaticMetadata,
    )
        requires
            old(pm).inv(),
            sm.valid(),
            sm.consistent_with_type::<L>(),
            sm.table.end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            Self::recover(pm@.read_state, Set::<u64>::empty(), *sm) == Some(ListTableSnapshot::<L>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        assume(false);
    }
}

}
