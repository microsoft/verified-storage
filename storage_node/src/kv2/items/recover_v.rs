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
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

pub(super) open spec fn item_recoverable<I>(
    s: Seq<u8>,
    addr: u64,
    sm: ItemTableStaticMetadata,
) -> bool
    where
        I: PmCopy,
{
    &&& sm.table.validate_row_addr(addr)
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

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub proof fn lemma_valid_depends_only_on_my_area(&self, old_jv: JournalView, new_jv: JournalView)
        requires
            self.valid(old_jv),
            old_jv.matches_in_range(new_jv, self@.sm.start() as int, self@.sm.end() as int),
            old_jv.constants == new_jv.constants,
        ensures
            self.valid(new_jv),
    {
        assume(false);
    }

    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        addrs: Set<u64>,
        sm: ItemTableStaticMetadata,
    )
        requires
            sm.valid::<I>(),
            sm.end() <= s1.len(),
            seqs_match_in_range(s1, s2, sm.start() as int, sm.end() as int),
            Self::recover(s1, addrs, sm) is Some,
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use group_validate_row_addr;
        assert(Self::recover(s1, addrs, sm) =~= Self::recover(s2, addrs, sm));
    }
}

}
