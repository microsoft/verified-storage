#![allow(unused_imports)]
pub mod abort_v;
pub mod append_v;
pub mod commit_v;
pub mod crud_v;
pub mod inv_v;
pub mod read_v;
pub mod recover_v;
pub mod spec_v;
pub mod start_v;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use append_v::*;
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
use read_v::*;
use spec_v::*;
use start_v::*;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

pub use spec_v::{ListTableSnapshot, ListTableView};

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
struct ListTableRowMetadata
{
    next_row_start: u64,
    num_block_elements: u64,
    num_trimmed_elements: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableStaticMetadata
{
    table: TableMetadata,
    num_lists_to_cache: u64,
    list_entry_size: u64,
    num_elements_per_block: u64,
    num_list_blocks: u64,
    row_size: u64,
    row_metadata_start: u64,
    row_metadata_end: u64,
    row_metadata_crc_start: u64,
    row_block_start: u64,
    row_block_end: u64,
    block_element_size: u64,
    block_element_list_entry_start: u64,
    block_element_list_entry_end: u64,
    block_element_crc_start: u64,
}

impl ListTableStaticMetadata
{
    pub closed spec fn valid<L>(self) -> bool
        where
            L: PmCopy,
    {
        &&& 0 < self.num_lists_to_cache
        &&& self.list_entry_size == L::spec_size_of()
        &&& self.table.valid()
        &&& self.table.start <= self.table.end
        &&& self.row_metadata_end - self.row_metadata_start == ListTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_block_start
        &&& self.num_elements_per_block * self.block_element_size <= self.row_block_end - self.row_block_start
        &&& self.block_element_list_entry_end - self.block_element_list_entry_start == self.list_entry_size
        &&& self.block_element_list_entry_end <= self.block_element_crc_start
        &&& self.block_element_crc_start + u64::spec_size_of() <= self.block_element_size
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
pub struct ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    status: Ghost<ListTableStatus>,
    sm: ListTableStaticMetadata,
    must_abort: Ghost<bool>,
    logical_range_gaps_policy: LogicalRangeGapsPolicy,
    durable_snapshot: Ghost<ListTableSnapshot<L>>,
    tentative_snapshot: Ghost<ListTableSnapshot<L>>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub closed spec fn view(&self) -> ListTableView<L>
    {
        ListTableView::<L>{
            sm: self.sm,
            logical_range_gaps_policy: self.logical_range_gaps_policy,
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
        sm: ListTableStaticMetadata,
    ) -> Option<ListTableSnapshot<L>>
    {
        arbitrary()
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        arbitrary()
    }

    pub exec fn space_needed_for_setup(ps: &SetupParameters, min_start: &OverflowingU64) -> (result: OverflowingU64)
        ensures
            result@ == Self::spec_space_needed_for_setup(*ps, min_start@),
    {
        assume(false);
        OverflowingU64::new(0)
    }

    pub exec fn setup(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<ListTableStaticMetadata, KvError>)
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, Set::<u64>::empty(), sm) == Some(ListTableSnapshot::<L>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.start() as int, sm.end() as int)
                    &&& sm.valid::<L>()
                    &&& min_start <= sm.start() <= sm.end() <= max_end
                    &&& sm.end() - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat)
                    &&& sm.num_rows() == ps.num_keys
                },
                Err(KvError::OutOfSpace) => max_end < Self::spec_space_needed_for_setup(*ps, min_start as nat),
                _ => false,
            },
    {
        assume(false);
        Err(KvError::OutOfSpace)
    }

    pub closed spec fn validate_list_addr(&self, addr: u64) -> bool
    {
        self.sm.table.validate_row_addr(addr)
    }

    pub open spec fn state_equivalent_for_me(&self, s: Seq<u8>, jv: JournalView) -> bool
    {
        &&& seqs_match_except_in_range(jv.durable_state, s, self@.sm.start() as int, self@.sm.end() as int)
        &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
        &&& j.constants == jv.constants
        &&& j.state == s
        &&& Self::recover(s, self@.durable.m.dom(), self@.sm) == Some(self@.durable)
    }
}

}
