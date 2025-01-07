#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
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

pub(super) open spec fn item_recoverable<I>(
    s: Seq<u8>,
    addr: u64,
    sm: ItemTableStaticMetadata,
) -> bool
    where
        I: PmCopy,
{
    &&& sm.table.validate_row_addr(addr as int)
    &&& recover_object::<I>(s, addr + sm.row_item_start, addr + sm.row_item_crc_start) is Some
}

pub(super) open spec fn items_recoverable<I>(
    s: Seq<u8>,
    addrs: Set<u64>,
    sm: ItemTableStaticMetadata,
) -> bool
    where
        I: PmCopy,
{
    forall|addr| #[trigger] addrs.contains(addr) ==> item_recoverable::<I>(s, addr, sm)
}

pub(super) open spec fn recover_item<I>(
    s: Seq<u8>,
    addr: u64,
    sm: ItemTableStaticMetadata,
) -> I
    where
        I: PmCopy,
    recommends
        item_recoverable::<I>(s, addr, sm),
{
    recover_object::<I>(s, addr + sm.row_item_start, addr + sm.row_item_crc_start).unwrap()
}

pub(super) open spec fn recover_items<I>(
    s: Seq<u8>,
    addrs: Set<u64>,
    sm: ItemTableStaticMetadata,
) -> Map::<u64, I>
    where
        I: PmCopy,
    recommends
        items_recoverable::<I>(s, addrs, sm),
{
    Map::<u64, I>::new(
        |addr: u64| addrs.contains(addr),
        |addr: u64| recover_item::<I>(s, addr, sm),
    )
}

pub(super) open spec fn local_recover<I>(
    s: Seq<u8>,
    addrs: Set<u64>,
    sm: ItemTableStaticMetadata,
) -> Option<ItemTableSnapshot<I>>
    where
        I: PmCopy,
{
    if items_recoverable::<I>(s, addrs, sm) {
        Some(ItemTableSnapshot::<I>{ m: recover_items::<I>(s, addrs, sm) })
    }
    else {
        None
    }
}

pub(super) proof fn lemma_local_recover_depends_only_on_item_area<I>(
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
        local_recover::<I>(s1, addrs, sm) is Some,
    ensures
        local_recover::<I>(s1, addrs, sm) == local_recover::<I>(s2, addrs, sm),
{
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    broadcast use group_validate_row_addr;
    assert(local_recover::<I>(s1, addrs, sm) =~= local_recover::<I>(s2, addrs, sm));
}

}
