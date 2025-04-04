#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::power_t::*;
use deps_hack::PmCopy;
use super::inv_v::*;
use super::spec_v::*;
use super::recover_v::*;
use super::super::spec_t::*;

verus! {

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
    pub open(super) spec fn valid<I>(self) -> bool
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
        
    pub open(super) spec fn spec_start(self) -> u64
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

    pub open(super) spec fn spec_end(self) -> u64
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

    pub open(super) spec fn num_rows(self) -> u64
    {
        self.table.num_rows
    }
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(I)]
pub struct ItemTable<PM, I>
where
    PM: PersistentMemoryRegion,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub(super) status: Ghost<ItemTableStatus>,
    pub(super) sm: ItemTableStaticMetadata,
    pub(super) must_abort: Ghost<bool>,
    pub(super) row_info: Ghost<Map<u64, ItemRowDisposition<I>>>,
    pub(super) free_list: Vec<u64>,
    pub(super) pending_allocations: Vec<u64>,
    pub(super) pending_deallocations: Vec<u64>,
    pub(super) phantom_pm: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, I> ItemTable<PM, I>
where
    PM: PersistentMemoryRegion,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub open(super) spec fn view(&self) -> ItemTableView<I>
    {
        ItemTableView::<I>{
            sm: self.sm,
            used_slots: self.sm.table.num_rows - self.free_list.len(),
            durable: self.internal_view().as_durable_snapshot(),
            tentative: if self.must_abort@ { None } else { Some(self.internal_view().as_tentative_snapshot()) },
        }
    }

    pub open(super) spec fn valid(self, jv: JournalView) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv(jv)
    }
    
    pub open(super) spec fn recover(
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

    pub open(super) spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        // let row_item_start = 0;
        let row_item_end = I::spec_size_of();
        let row_item_crc_end = row_item_end + u64::spec_size_of();
        let row_size = row_item_crc_end;
        let num_rows = ps.max_keys;
        let table_size = num_rows as int * row_size;
        let initial_space = if min_start > u64::MAX { 0 } else {
            space_needed_for_alignment(min_start as int, u64::spec_size_of() as int)
        };
        (initial_space + table_size) as nat
    }

    pub open(super) spec fn validate_item_addr(&self, addr: u64) -> bool
    {
        self.sm.table.validate_row_addr(addr)
    }

    pub open spec fn state_equivalent_for_me_specific(
        s: Seq<u8>,
        item_addrs: Set<u64>,
        durable_state: Seq<u8>,
        constants: JournalConstants,
        sm: ItemTableStaticMetadata
    ) -> bool
    {
        &&& seqs_match_except_in_range(durable_state, s, sm.start() as int, sm.end() as int)
        &&& Journal::<PM>::state_recovery_idempotent(s, constants)
        &&& Self::recover(s, item_addrs, sm) == Self::recover(durable_state, item_addrs, sm)
    }

    pub open spec fn state_equivalent_for_me(&self, s: Seq<u8>, jv: JournalView) -> bool
    {
        Self::state_equivalent_for_me_specific(s, self@.durable.m.dom(), jv.durable_state, jv.constants, self@.sm)
    }
}

}
