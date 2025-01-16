#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use deps_hack::PmCopy;
use inv_v::*;
use start_v::*;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::spec_t::*;

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
        Self{ m: Map::<u64, Seq<L>>::new(|list_addr: u64| list_addr == 0, |list_addr: u64| Seq::<L>::empty()) }
    }

    pub open spec fn delete(&self, list_addr: u64) -> Self
    {
        Self{ m: self.m.remove(list_addr) }
    }
}

#[verifier::ext_equal]
pub struct ListTableView<L>
{
    pub sm: ListTableStaticMetadata,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub durable: ListTableSnapshot<L>,
    pub tentative: Option<ListTableSnapshot<L>>,
}

}
