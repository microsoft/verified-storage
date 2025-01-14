#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::inv_v::*;
use super::recover_v::*;
use super::setup_v::*;
use super::start_v::*;

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

    pub open spec fn create(&self, item_addr: u64, item: I) -> Self
    {
        Self{ m: self.m.insert(item_addr, item) }
    }

    pub open spec fn delete(&self, item_addr: u64) -> Self
    {
        Self{ m: self.m.remove(item_addr) }
    }

}

#[verifier::ext_equal]
pub struct ItemTableView<I>
{
    pub sm: ItemTableStaticMetadata,
    pub durable: ItemTableSnapshot<I>,
    pub tentative: Option<ItemTableSnapshot<I>>,
}

}


