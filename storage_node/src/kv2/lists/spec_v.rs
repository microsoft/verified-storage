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

    pub open spec fn append(&self, old_list_addr: u64, new_list_addr: u64, new_list_entry: L) -> Self
    {
        let new_list = self.m[old_list_addr].push(new_list_entry);
        Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
    }

    pub open spec fn create_singleton(&self, new_list_addr: u64, new_list_entry: L) -> Self
    {
        Self{ m: self.m.insert(new_list_addr, seq![new_list_entry]) }
    }

    pub open spec fn update_entry_at_index(&self, old_list_addr: u64, new_list_addr: u64, idx: usize,
                                           new_list_entry: L) -> Self
    {
        let new_list = self.m[old_list_addr].update(idx as int, new_list_entry);
        Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
    }

    pub open spec fn trim(&self, old_list_addr: u64, new_list_addr: u64, trim_length: usize) -> Self
    {
        if new_list_addr == 0 {
            Self{ m: self.m.remove(old_list_addr) }
        }
        else {
            let new_list = self.m[old_list_addr].skip(trim_length as int);
            Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
        }
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
