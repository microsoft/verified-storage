#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::items_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ItemTableStaticMetadata
{
    pub table: TableMetadata,
    pub item_size: u64,
    pub row_item_start: u64,
    pub row_item_end: u64,
    pub row_item_crc_start: u64,
}

impl ItemTableStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.table.valid()
        &&& self.table.start <= self.table.end
        &&& self.row_item_end - self.row_item_start == self.item_size
        &&& self.row_item_end <= self.row_item_crc_start
        &&& self.row_item_crc_start + u64::spec_size_of() <= self.table.row_size
    }

    pub open spec fn consistent_with_type<I>(self) -> bool
        where
            I: PmCopy,
    {
        &&& self.item_size == I::spec_size_of()
    }
}

pub(super) open spec fn recover_items<I>(
    s: Seq<u8>,
    addrs: Set<u64>,
    sm: ItemTableStaticMetadata,
) -> Option<ItemTableSnapshot<I>>
    where
        I: PmCopy,
{
    arbitrary()
}

pub(super) proof fn lemma_recover_items_depends_only_on_item_area<I>(
    s1: Seq<u8>,
    s2: Seq<u8>,
    addrs: Set<u64>,
    sm: ItemTableStaticMetadata,
)
    where
        I: PmCopy,
    requires
        sm.valid(),
        sm.consistent_with_type::<I>(),
        sm.table.end <= s1.len(),
        seqs_match_in_range(s1, s2, sm.table.start as int, sm.table.end as int),
        recover_items::<I>(s1, addrs, sm) is Some,
    ensures
        recover_items::<I>(s1, addrs, sm) == recover_items::<I>(s2, addrs, sm),
{
    assume(false);
}

}
