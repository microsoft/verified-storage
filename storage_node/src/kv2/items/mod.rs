#![allow(unused_imports)]

mod abort_v;
mod commit_v;
mod inv_v;
mod recover_v;
mod setup_v;
mod start_v;

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
use inv_v::*;
use recover_v::*;
use setup_v::*;
use start_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::impl_t::*;
use super::recover_v::*;
use super::spec_t::*;

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

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ItemTableStaticMetadata
{
    pub(super) table: TableMetadata,
    pub(super) item_size: u64,
    pub(super) row_item_start: u64,
    pub(super) row_item_end: u64,
    pub(super) row_item_crc_start: u64,
}

impl ItemTableStaticMetadata
{
    pub closed spec fn valid<I>(self) -> bool
        where
            I: PmCopy,
    {
        &&& self.table.valid()
        &&& self.table.start <= self.table.end
        &&& self.row_item_end - self.row_item_start == self.item_size
        &&& self.row_item_end <= self.row_item_crc_start
        &&& self.row_item_crc_start + u64::spec_size_of() <= self.table.row_size
        &&& self.item_size == I::spec_size_of()
    }
        
    pub closed spec fn spec_start(self) -> u64
    {
        self.table.start
    }

    #[verifier::when_used_as_spec(spec_start)]
    pub exec fn start(self) -> (result: u64)
        ensures
            result == self.spec_start(),
    {
        self.table.start
    }

    pub closed spec fn spec_end(self) -> u64
    {
        self.table.end
    }

    #[verifier::when_used_as_spec(spec_end)]
    pub exec fn end(self) -> (result: u64)
        ensures
            result == self.spec_end(),
    {
        self.table.end
    }

    pub closed spec fn num_rows(self) -> u64
    {
        self.table.num_rows
    }
}

#[verifier::ext_equal]
pub struct ItemTableView<I>
{
    pub sm: ItemTableStaticMetadata,
    pub durable: ItemTableSnapshot<I>,
    pub tentative: Option<ItemTableSnapshot<I>>,
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(I)]
pub struct ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    status: Ghost<ItemTableStatus>,
    sm: ItemTableStaticMetadata,
    must_abort: Ghost<bool>,
    durable_snapshot: Ghost<ItemTableSnapshot<I>>,
    tentative_snapshot: Ghost<ItemTableSnapshot<I>>,
    free_list: Vec<u64>,
    pending_deallocations: Vec<u64>,
    phantom_pm: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub closed spec fn view(&self) -> ItemTableView<I>
    {
        ItemTableView::<I>{
            sm: self.sm,
            durable: self.durable_snapshot@,
            tentative: if self.must_abort@ { None } else { Some(self.tentative_snapshot@) },
        }
    }

    pub closed spec fn valid(self, jv: JournalView) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv(jv)
    }
    
    pub closed spec fn recover(
        s: Seq<u8>,
        addrs: Set<u64>,
        sm: ItemTableStaticMetadata,
    ) -> Option<ItemTableSnapshot<I>>
    {
        if items_recoverable::<I>(s, addrs, sm) {
            Some(ItemTableSnapshot::<I>{ m: recover_items::<I>(s, addrs, sm) })
        }
        else {
            None
        }
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        // let row_item_start = 0;
        let row_item_end = I::spec_size_of();
        let row_item_crc_end = row_item_end + u64::spec_size_of();
        let row_size = row_item_crc_end;
        let num_rows = ps.num_keys;
        let table_size = num_rows as int * row_size;
        let initial_space = if min_start > u64::MAX { 0 } else {
            space_needed_for_alignment(min_start as int, u64::spec_size_of() as int)
        };
        (initial_space + table_size) as nat
    }

}

}


