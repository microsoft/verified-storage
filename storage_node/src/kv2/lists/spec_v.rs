#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::ListTableStaticMetadata;
use super::super::spec_t::*;

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

    pub open spec fn delete(&self, list_addr: u64) -> Self
    {
        Self{ m: self.m.remove(list_addr) }
    }

    pub open spec fn append(&self, old_list_addr: u64, new_list_addr: u64, new_element: L) -> Self
    {
        let new_list = self.m[old_list_addr].push(new_element);
        Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
    }

    pub open spec fn create_singleton(&self, new_list_addr: u64, new_element: L) -> Self
    {
        Self{ m: self.m.insert(new_list_addr, seq![new_element]) }
    }

    pub open spec fn update_element_at_index(&self, old_list_addr: u64, new_list_addr: u64, idx: usize,
                                             new_element: L) -> Self
    {
        let new_list = self.m[old_list_addr].update(idx as int, new_element);
        Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
    }

    pub open spec fn trim(&self, old_list_addr: u64, new_list_addr: u64, trim_length: int) -> Self
    {
        if new_list_addr == 0 {
            Self{ m: self.m.remove(old_list_addr) }
        }
        else {
            let new_list = self.m[old_list_addr].skip(trim_length);
            Self{ m: self.m.remove(old_list_addr).insert(new_list_addr, new_list) }
        }
    }
}

#[verifier::ext_equal]
pub struct ListTableView<L>
{
    pub sm: ListTableStaticMetadata,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub used_slots: int,
    pub durable: ListTableSnapshot<L>,
    pub tentative: Option<ListTableSnapshot<L>>,
}

}
