#![allow(unused_imports)]
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
use pmcopy::PmCopy;
use std::collections::hash_map::HashMap;
use super::inv_v::*;
use super::recover_v::*;
use super::spec_v::*;
use super::super::spec_t::*;

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableStaticMetadata
{
    pub(super) table: TableMetadata,
    pub(super) element_size: u64,
    pub(super) row_next_start: u64,
    pub(super) row_element_start: u64,
    pub(super) row_element_crc_start: u64,
}

impl ListTableStaticMetadata
{
    pub open(super) spec fn valid<L>(self) -> bool
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
#[verifier::reject_recursive_types(L)]
pub struct ListTable<PM, L>
where
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) status: Ghost<ListTableStatus>,
    pub(super) sm: ListTableStaticMetadata,
    pub(super) must_abort: Ghost<bool>,
    pub(super) logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub(super) space_needed_to_journal_next: u64,
    pub(super) durable_mapping: Ghost<ListRecoveryMapping<L>>,
    pub(super) tentative_mapping: Ghost<ListRecoveryMapping<L>>,
    pub(super) row_info: Ghost<Map<u64, ListRowDisposition>>,
    pub(super) m: HashMap<u64, ListTableEntry<L>>,
    pub(super) deletes_inverse: Ghost<Map<u64, nat>>,
    pub(super) deletes: Vec<ListSummary>,
    pub(super) modifications: Vec<Option<u64>>,
    pub(super) free_list: Vec<u64>,
    pub(super) pending_allocations: Vec<u64>,
    pub(super) pending_deallocations: Vec<u64>,
    pub(super) phantom_pm: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, L> ListTable<PM, L>
where
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub open(super) spec fn view(&self) -> ListTableView<L>
    {
        ListTableView::<L>{
            sm: self.sm,
            logical_range_gaps_policy: self.logical_range_gaps_policy,
            used_slots: self.sm.table.num_rows - self.free_list.len(),
            durable: self.durable_mapping@.as_snapshot(),
            tentative: if self.must_abort@ { None } else { Some(self.tentative_mapping@.as_snapshot()) },
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
        sm: ListTableStaticMetadata,
    ) -> Option<ListTableSnapshot<L>>
    {
        match ListRecoveryMapping::<L>::new(s, addrs, sm) {
            None => None,
            Some(mapping) => Some(mapping.as_snapshot())
        }
    }
    
    pub open(super) spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
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

    pub open(super) spec fn validate_list_addr(&self, addr: u64) -> bool
    {
        self.sm.table.validate_row_addr(addr)
    }

    pub open spec fn state_equivalent_for_me(
        s: Seq<u8>,
        durable_state: Seq<u8>,
        list_addrs: Set<u64>,
        constants: JournalConstants,
        sm: ListTableStaticMetadata
    ) -> bool
    {
        &&& seqs_match_except_in_range(durable_state, s, sm.start() as int, sm.end() as int)
        &&& Journal::<PM>::state_recovery_idempotent(s, constants)
        &&& Self::recover(s, list_addrs, sm) == Self::recover(durable_state, list_addrs, sm)
    }

    pub open spec fn perm_factory_permits_states_equivalent_for_me<PermFactory>(
        &self,
        jv: JournalView,
        perm_factory: PermFactory
    ) -> bool
        where
            PermFactory: PermissionFactory<Seq<u8>>,
    {
        forall|s1: Seq<u8>, s2: Seq<u8>| {
            &&& Self::state_equivalent_for_me(s1, jv.durable_state, self@.durable.m.dom(), jv.constants, self@.sm)
            &&& Self::state_equivalent_for_me(s2, jv.durable_state, self@.durable.m.dom(), jv.constants, self@.sm)
        } ==> #[trigger] perm_factory.permits(s1, s2)
    }
}

}
