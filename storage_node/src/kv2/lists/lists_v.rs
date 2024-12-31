#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::super::kvimpl_t::*;
use super::super::kvshared_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::ext_equal]
pub struct ListTableSnapshot<L>
{
    pub m: Map<int, L>,
}

impl<L> ListTableSnapshot<L>
{
    pub open spec fn init() -> Self
    {
        Self{ m: Map::<int, L>::empty() }
    }
}

#[verifier::ext_equal]
pub struct ListTableView<L>
{
    pub durable: ListTableSnapshot<L>,
    pub tentative: ListTableSnapshot<L>,
}

impl<L> ListTableView<L>
{
    pub open spec fn init() -> Self
    {
        Self {
            durable: ListTableSnapshot::<L>::init(),
            tentative: ListTableSnapshot::<L>::init(),
        }
    }
}

#[verifier::ext_equal]
pub struct ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + Sized + std::fmt::Debug,
{
    m: Map<u64, Vec<L>>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + Sized + std::fmt::Debug,
{
    pub open spec fn recover(
        s: Seq<u8>,
        config: KvConfiguration
    ) -> Option<ListTableView<L>>
    {
        None
    }

    pub exec fn setup(
        pm: &mut PM,
        config: &KvConfiguration,
    )
        ensures
            pm@.valid(),
            Self::recover(pm@.read_state, *config) == Some(ListTableView::<L>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, config.list_table_start as int,
                                       config.list_table_end as int),
    {
        assume(false);
    }
}

}
