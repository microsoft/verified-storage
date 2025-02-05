#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
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
use recover_v::*;
use std::collections::HashSet;
use std::hash::Hash;
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn read_list(
        journal: &Journal<TrustedKvPermission, PM>,
        sm: &ListTableStaticMetadata,
        Ghost(list_addrs): Ghost<Set<u64>>,
        Ghost(mapping): Ghost<ListRecoveryMapping<L>>,
        row_addrs_used: &mut HashSet<u64>,
        list_addr: u64,
    ) -> (result: Result<ListTableDurableEntry, KvError>)
        requires
            journal.valid(),
            journal@.constants.app_area_start <= sm.start(),
            sm.end() <= journal@.constants.app_area_end,
            sm.valid::<L>(),
            mapping.corresponds(journal@.read_state, list_addrs, *sm),
            list_addrs.contains(list_addr),
            mapping.list_info.contains_key(list_addr),
            list_addr != 0,
        ensures
            match result {
                Ok(entry) => {
                    let row_addrs = mapping.list_info[list_addr];
                    &&& forall|row_addr: u64| #[trigger] old(row_addrs_used)@.contains(row_addr)
                            ==> row_addrs_used@.contains(row_addr)
                    &&& forall|i: int| 0 <= i < row_addrs.len()
                           ==> row_addrs_used@.contains(#[trigger] row_addrs[i])
                    &&& forall|row_addr: u64| #[trigger] row_addrs_used@.contains(row_addr)
                            ==> {
                                ||| old(row_addrs_used)@.contains(row_addr)
                                ||| row_addrs.contains(row_addr)
                            }
                    &&& 0 < row_addrs.len()
                    &&& entry.head == row_addrs[0]
                    &&& entry.tail == row_addrs.last()
                    &&& entry.length == row_addrs.len()
                    &&& mapping.row_info.contains_key(entry.tail)
                    &&& entry.end_of_logical_range == mapping.row_info[entry.tail].element.end()
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        proof {
            journal.lemma_valid_implications();
        }

        let mut current_addr = list_addr;
        let pm = journal.get_pm_region_ref();
        let mut num_elements_processed: usize = 0;
        let ghost row_addrs = mapping.list_info[list_addr];
        let ghost elements = mapping.list_elements[list_addr];
        
        loop
            invariant
                sm.valid::<L>(),
                sm.table.end <= pm@.len(),
                sm.table.end <= journal@.constants.app_area_end, // and thus all our addresses fit in a `u64`
                current_addr != 0,
                num_elements_processed < row_addrs.len(),
                row_addrs.len() <= usize::MAX,
                current_addr == row_addrs[num_elements_processed as int],
                mapping.corresponds(pm@.read_state, list_addrs, *sm),
                list_addrs.contains(list_addr),
                mapping.list_info.contains_key(list_addr),
                row_addrs == mapping.list_info[list_addr],
                elements == mapping.list_elements[list_addr],
                pm.inv(),
                pm.constants() == journal@.pm_constants,
                forall|row_addr: u64| #[trigger] old(row_addrs_used)@.contains(row_addr)
                    ==> row_addrs_used@.contains(row_addr),
                forall|i: int| 0 <= i < num_elements_processed ==> row_addrs_used@.contains(#[trigger] row_addrs[i]),
                forall|row_addr: u64| #[trigger] row_addrs_used@.contains(row_addr) ==> {
                    ||| old(row_addrs_used)@.contains(row_addr)
                    ||| row_addrs.contains(row_addr)
                },
            decreases
                row_addrs.len() - num_elements_processed,
        {
            broadcast use group_hash_axioms;
            broadcast use group_validate_row_addr;

            assert(sm.table.validate_row_addr(current_addr));
            assert(row_addrs.contains(current_addr));
            row_addrs_used.insert(current_addr);

            let next_addr = match exec_recover_object::<PM, u64>(pm, current_addr + sm.row_next_start,
                                                                 current_addr + sm.row_next_crc_start) {
                Some(n) => n,
                None => { return Err(KvError::CRCMismatch); },
            };

            if next_addr == 0 {
                let element = match exec_recover_object::<PM, L>(pm, current_addr + sm.row_element_start,
                                                                 current_addr + sm.row_element_crc_start) {
                    Some(e) => e,
                    None => { return Err(KvError::CRCMismatch); },
                };
                let entry = ListTableDurableEntry{
                    head: list_addr,
                    tail: current_addr,
                    length: num_elements_processed + 1,
                    end_of_logical_range: element.end(),
                };
                return Ok(entry);
            }

            current_addr = next_addr;
            num_elements_processed = num_elements_processed + 1;
        }
    }

    exec fn read_all_lists(
        journal: &Journal<TrustedKvPermission, PM>,
        sm: &ListTableStaticMetadata,
        list_addrs: &Vec<u64>,
        Ghost(mapping): Ghost<ListRecoveryMapping<L>>,
    ) -> (result: Result<(HashSet<u64>, HashMap<u64, ListTableEntry<L>>), KvError>)
        requires
            journal.valid(),
            journal@.constants.app_area_start <= sm.start(),
            sm.end() <= journal@.constants.app_area_end,
            sm.valid::<L>(),
            mapping.corresponds(journal@.read_state, list_addrs@.to_set(), *sm),
            forall|list_addr: u64| #[trigger] list_addrs@.contains(list_addr)
                <==> mapping.list_info.contains_key(list_addr),
            !list_addrs@.contains(0),
        ensures
            match result {
                Ok((row_addrs_used, m)) => {
                    &&& forall|row_addr: u64| mapping.row_info.contains_key(row_addr)
                            <==> #[trigger] row_addrs_used@.contains(row_addr)
                    &&& forall|list_addr: u64| #[trigger] m@.contains_key(list_addr) ==>
                            mapping.list_info.contains_key(list_addr)
                    &&& forall|list_addr: u64| #[trigger] mapping.list_info.contains_key(list_addr) ==> {
                        let row_addrs = mapping.list_info[list_addr];
                        let entry = m@[list_addr]->Durable_entry;
                        &&& 0 < row_addrs.len()
                        &&& m@.contains_key(list_addr)
                        &&& m@[list_addr] is Durable
                        &&& entry.head == row_addrs[0]
                        &&& entry.tail == row_addrs.last()
                        &&& entry.length == row_addrs.len()
                        &&& mapping.row_info.contains_key(entry.tail)
                        &&& entry.end_of_logical_range == mapping.row_info[entry.tail].element.end()
                    }
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        let mut row_addrs_used = HashSet::<u64>::new();
        let mut m = HashMap::<u64, ListTableEntry<L>>::new();
        let num_lists = list_addrs.len();
        for which_list in 0..num_lists
            invariant
                journal.valid(),
                journal@.constants.app_area_start <= sm.start(),
                sm.end() <= journal@.constants.app_area_end,
                sm.valid::<L>(),
                !list_addrs@.contains(0),
                num_lists == list_addrs.len(),
                mapping.corresponds(journal@.read_state, list_addrs@.to_set(), *sm),
                forall|i: int, j: int| #![trigger mapping.list_info[list_addrs@[i]][j]] 0 <= i < which_list ==> {
                    let row_addrs = mapping.list_info[list_addrs@[i]];
                    &&& mapping.list_info.contains_key(list_addrs@[i])
                    &&& 0 <= j < row_addrs.len() ==> row_addrs_used@.contains(row_addrs[j])
                },
                forall|row_addr: u64| #[trigger] row_addrs_used@.contains(row_addr)
                    ==> mapping.row_info.contains_key(row_addr),
                forall|list_addr: u64| #[trigger] m@.contains_key(list_addr) ==>
                    mapping.list_info.contains_key(list_addr),
                forall|i: int| #![trigger list_addrs@[i]] 0 <= i < which_list ==> {
                    let list_addr = list_addrs@[i];
                    let row_addrs = mapping.list_info[list_addr];
                    let entry = m@[list_addr]->Durable_entry;
                    &&& 0 < row_addrs.len()
                    &&& m@.contains_key(list_addr)
                    &&& m@[list_addr] is Durable
                    &&& entry.head == row_addrs[0]
                    &&& entry.tail == row_addrs.last()
                    &&& entry.length == row_addrs.len()
                    &&& mapping.row_info.contains_key(entry.tail)
                    &&& entry.end_of_logical_range == mapping.row_info[entry.tail].element.end()
                }
        {
            broadcast use group_hash_axioms;

            let ghost old_m = m@;

            let list_addr = list_addrs[which_list];
            assert(list_addrs@.to_set().contains(list_addr));
            assert(mapping.list_info.contains_key(list_addr));
            match Self::read_list(journal, sm, Ghost(list_addrs@.to_set()), Ghost(mapping),
                                  &mut row_addrs_used, list_addr) {
                Ok(entry) => { m.insert(list_addr, ListTableEntry::Durable{ entry }); },
                Err(e) => return Err(e),
            };
        }

        Ok((row_addrs_used, m))
    }

    exec fn build_free_list(
        row_addrs_used: &HashSet<u64>,
        sm: &ListTableStaticMetadata
    ) -> (result: (Vec<u64>, Ghost<Map<u64, ListRowDisposition>>))
        requires
            sm.valid::<L>(),
        ensures
        ({
            let (free_list, Ghost(row_info)) = result;
            &&& forall|row_addr: u64| sm.table.validate_row_addr(row_addr) ==> #[trigger] row_info.contains_key(row_addr)
            &&& forall|row_addr: u64| #[trigger] row_info.contains_key(row_addr) ==>
                match row_info[row_addr] {
                    ListRowDisposition::InFreeList{ pos } => {
                        &&& 0 <= pos < free_list@.len()
                        &&& free_list@[pos as int] == row_addr
                        &&& !row_addrs_used@.contains(row_addr)
                    },
                    ListRowDisposition::NowhereFree => row_addrs_used@.contains(row_addr),
                    _ => false,
                }
            &&& forall|i: int| #![trigger free_list@[i]] 0 <= i < free_list@.len() ==> {
                    let row_addr = free_list@[i];
                    &&& sm.table.validate_row_addr(row_addr)
                    &&& row_info.contains_key(row_addr)
                    &&& row_info[row_addr] matches ListRowDisposition::InFreeList{ pos }
                    &&& pos == i
                }
        })
    {
        let mut free_list = Vec::<u64>::new();
        let ghost row_info = Map::<u64, ListRowDisposition>::empty();
        let mut row_index: u64 = 0;
        let mut row_addr = sm.table.start;
    
        proof {
            sm.table.lemma_start_is_valid_row();
        }

        for row_index in 0..sm.table.num_rows
            invariant
                sm.valid::<L>(),
                sm.table.row_addr_to_index(row_addr) == row_index as int,
                sm.table.start <= row_addr <= sm.table.end,
                row_index < sm.table.num_rows ==> sm.table.validate_row_addr(row_addr),
                forall|any_row_addr: u64| {
                    &&& sm.table.validate_row_addr(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                } ==> #[trigger] row_info.contains_key(any_row_addr),
                forall|i: int| #![trigger free_list@[i]] 0 <= i < free_list@.len() ==> {
                    let row_addr = free_list@[i];
                    &&& sm.table.validate_row_addr(row_addr)
                    &&& row_info.contains_key(row_addr)
                    &&& row_info[row_addr] matches ListRowDisposition::InFreeList{ pos }
                    &&& pos == i
                },
                forall|row_addr: u64| #[trigger] row_info.contains_key(row_addr) ==>
                    match row_info[row_addr] {
                        ListRowDisposition::InFreeList{ pos } => {
                            &&& 0 <= pos < free_list@.len()
                            &&& free_list@[pos as int] == row_addr
                            &&& !row_addrs_used@.contains(row_addr)
                        },
                        ListRowDisposition::NowhereFree => row_addrs_used@.contains(row_addr),
                        _ => false,
                    },
                forall|i: int| 0 <= i < free_list@.len() ==>
                    0 <= sm.table.row_addr_to_index(#[trigger] free_list@[i]) < row_index,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                sm.table.lemma_row_addr_successor_is_valid(row_addr);
            }

            let ghost old_free_list = free_list@;
            if row_addrs_used.contains(&row_addr) {
                proof {
                    row_info = row_info.insert(row_addr, ListRowDisposition::NowhereFree);
                }
            }
            else {
                proof {
                    let ghost pos = free_list@.len();
                    row_info = row_info.insert(row_addr, ListRowDisposition::InFreeList{ pos });
                }
                free_list.push(row_addr);
            }

            row_addr = row_addr + sm.table.row_size;
        }
    
        assert forall|row_addr: u64| sm.table.validate_row_addr(row_addr)
                                implies #[trigger] row_info.contains_key(row_addr) by {
            let row_index = sm.table.row_addr_to_index(row_addr);
            broadcast use group_validate_row_addr;
        }

        (free_list, Ghost(row_info))
    }

    pub exec fn start(
        journal: &Journal<TrustedKvPermission, PM>,
        logical_range_gaps_policy: LogicalRangeGapsPolicy,
        list_addrs: &Vec<u64>,
        sm: &ListTableStaticMetadata,
    ) -> (result: Result<Self, KvError>)
        requires
            journal.valid(),
            journal.recover_idempotent(),
            journal@.valid(),
            journal@.journaled_addrs == Set::<int>::empty(),
            journal@.durable_state == journal@.read_state,
            journal@.read_state == journal@.commit_state,
            journal@.constants.app_area_start <= sm.start(),
            sm.end() <= journal@.constants.app_area_end,
            0 < sm.start(), // so that `0` isn't a valid address and can be used as a sentinel
            Self::recover(journal@.read_state, list_addrs@.to_set(), *sm) is Some,
            sm.valid::<L>(),
            !list_addrs@.contains(0),
        ensures
            match result {
                Ok(lists) => {
                    let recovered_state =
                        Self::recover(journal@.read_state, list_addrs@.to_set(), *sm).unwrap();
                    &&& lists.valid(journal@)
                    &&& lists@.sm == *sm
                    &&& lists@.logical_range_gaps_policy == logical_range_gaps_policy
                    &&& lists@.durable == recovered_state
                    &&& lists@.tentative == Some(recovered_state)
                    &&& recovered_state.m.dom() == list_addrs@.to_set()
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            }
    {
        let ghost mapping = ListRecoveryMapping::<L>::new(journal@.read_state, list_addrs@.to_set(), *sm).unwrap();
        assert(forall|list_addr: u64|
               #[trigger] list_addrs@.contains(list_addr) <==> list_addrs@.to_set().contains(list_addr));
        let (row_addrs_used, m) = match Self::read_all_lists(journal, sm, list_addrs, Ghost(mapping)) {
            Ok(rm) => rm,
            Err(e) => { return Err(e); },
        };
        let (free_list, Ghost(row_info)) = Self::build_free_list(&row_addrs_used, sm);

        let lists = Self{
            status: Ghost(ListTableStatus::Quiescent),
            sm: *sm,
            must_abort: Ghost(false),
            logical_range_gaps_policy,
            durable_list_addrs: Ghost(list_addrs@.to_set()),
            tentative_list_addrs: Ghost(list_addrs@.to_set()),
            durable_mapping: Ghost(mapping),
            tentative_mapping: Ghost(mapping),
            row_info: Ghost(row_info),
            m,
            deletes_inverse: Ghost(Map::<u64, nat>::empty()),
            deletes: Vec::<ListTableDurableEntry>::new(),
            updates: Vec::<Option<u64>>::new(),
            creates: Vec::<Option<u64>>::new(),
            free_list,
            pending_allocations: Vec::<u64>::new(),
            pending_deallocations: Vec::<u64>::new(),
            phantom: Ghost(core::marker::PhantomData),
        };

        let ghost recovered_state = Self::recover(journal@.read_state, list_addrs@.to_set(), *sm).unwrap();
        assert(recovered_state.m.dom() =~= list_addrs@.to_set());

        Ok(lists)
    }
}

}

