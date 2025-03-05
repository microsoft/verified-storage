#![allow(unused_imports)]
pub mod abort_v;
pub mod append_v;
pub mod commit_v;
pub mod delete_v;
pub mod inv_v;
pub mod read_v;
pub mod recover_v;
pub mod setup_v;
pub mod slots_v;
pub mod spec_v;
pub mod start_v;
pub mod trim_v;
pub mod update_v;
pub mod util_v;

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
use recover_v::*;
use spec_v::*;
use start_v::*;
use std::collections::hash_map::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

pub use spec_v::{ListTableSnapshot, ListTableView};

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableStaticMetadata
{
    table: TableMetadata,
    element_size: u64,
    row_next_start: u64,
    row_element_start: u64,
    row_element_crc_start: u64,
}

impl ListTableStaticMetadata
{
    pub closed spec fn valid<L>(self) -> bool
        where
            L: PmCopy,
    {
        &&& self.element_size == L::spec_size_of()
        &&& self.table.valid()
        &&& self.table.start <= self.table.end
        &&& self.row_next_start + u64::spec_size_of() + u64::spec_size_of() <= self.row_element_start
        &&& self.row_element_start + self.element_size <= self.row_element_crc_start
        &&& self.row_element_crc_start + u64::spec_size_of() <= self.table.row_size
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
#[verifier::reject_recursive_types(L)]
pub struct ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    status: Ghost<ListTableStatus>,
    sm: ListTableStaticMetadata,
    must_abort: Ghost<bool>,
    logical_range_gaps_policy: LogicalRangeGapsPolicy,
    space_needed_to_journal_next: u64,
    durable_mapping: Ghost<ListRecoveryMapping<L>>,
    tentative_mapping: Ghost<ListRecoveryMapping<L>>,
    row_info: Ghost<Map<u64, ListRowDisposition>>,
    m: HashMap<u64, ListTableEntry<L>>,
    deletes_inverse: Ghost<Map<u64, nat>>,
    deletes: Vec<ListSummary>,
    modifications: Vec<Option<u64>>,
    free_list: Vec<u64>,
    pending_allocations: Vec<u64>,
    pending_deallocations: Vec<u64>,
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
            used_slots: self.sm.table.num_rows - self.free_list.len(),
            durable: self.durable_mapping@.as_snapshot(),
            tentative: if self.must_abort@ { None } else { Some(self.tentative_mapping@.as_snapshot()) },
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
        match ListRecoveryMapping::<L>::new(s, addrs, sm) {
            None => None,
            Some(mapping) => Some(mapping.as_snapshot())
        }
    }
    
    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
        recommends
            ps.valid(),
    {
        // let row_next_start = 0;
        let row_element_start = u64::spec_size_of() + u64::spec_size_of();
        let row_element_crc_start = row_element_start + L::spec_size_of();
        let row_size = row_element_crc_start + u64::spec_size_of();
        let num_rows = ps.max_list_elements;
        let table_size = num_rows as int * row_size;
        let initial_space = if min_start > u64::MAX { 0 } else {
            space_needed_for_alignment(min_start as int, u64::spec_size_of() as int)
        };
        (initial_space + table_size) as nat
    }

    pub closed spec fn validate_list_addr(&self, addr: u64) -> bool
    {
        self.sm.table.validate_row_addr(addr)
    }

    pub open spec fn state_equivalent_for_me_specific(
        s: Seq<u8>,
        list_addrs: Set<u64>,
        durable_state: Seq<u8>,
        constants: JournalConstants,
        sm: ListTableStaticMetadata
    ) -> bool
    {
        &&& seqs_match_except_in_range(durable_state, s, sm.start() as int, sm.end() as int)
        &&& Journal::<TrustedKvPermission, PM>::state_recovery_idempotent(s, constants)
        &&& Self::recover(s, list_addrs, sm) == Self::recover(durable_state, list_addrs, sm)
    }

    pub open spec fn state_equivalent_for_me(&self, s: Seq<u8>, jv: JournalView) -> bool
    {
        Self::state_equivalent_for_me_specific(s, self@.durable.m.dom(), jv.durable_state, jv.constants, self@.sm)
    }
}

}
