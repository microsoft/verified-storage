#![allow(unused_imports)]
use vstd::prelude::*;

use crate::common::table_v::*;
use crate::journal::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::power_t::*;
use std::collections::HashSet;
use super::{ItemTable, ItemTableStaticMetadata};
use super::inv_v::*;
use super::recover_v::*;
use super::super::spec_t::*;

verus! {

impl<PM, I> ItemTable<PM, I>
where
    PM: PersistentMemoryRegion,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start(
        journal: &Journal<PM>,
        item_addrs: &HashSet<u64>,
        sm: &ItemTableStaticMetadata,
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
            Self::recover(journal@.read_state, item_addrs@, *sm) is Some,
            sm.valid::<I>(),
        ensures
            match result {
                Ok(items) => {
                    let recovered_state = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
                    &&& items.valid(journal@)
                    &&& items@.sm == *sm
                    &&& recovered_state.m.dom().finite()
                    &&& items@.used_slots == recovered_state.m.dom().len()
                    &&& items@.durable == recovered_state
                    &&& items@.tentative == Some(recovered_state)
                    &&& recovered_state.m.dom() == item_addrs@
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            }
    {
        // The item table does not modify (or even read) any durable data during start.
        // The only thing we have to do here is fill in its free list and initialize
        // other associated data structures.

        let ghost mut row_info = Map::<u64, ItemRowDisposition<I>>::empty();
        let mut free_list: Vec<u64> = Vec::new();
        let mut row_index: u64 = 0;
        let mut row_addr: u64 = sm.table.start;
    
        proof {
            sm.table.lemma_start_is_valid_row();
        }

        while row_index < sm.table.num_rows
            invariant
                Self::recover(journal@.read_state, item_addrs@, *sm) is Some,
                sm.valid::<I>(),
                0 <= row_index <= sm.table.num_rows,
                sm.table.row_addr_to_index(row_addr) == row_index as int,
                sm.table.start <= row_addr <= sm.table.end,
                row_index < sm.table.num_rows ==> sm.table.validate_row_addr(row_addr),
                journal@.constants.app_area_start <= sm.start(),
                sm.end() <= journal@.constants.app_area_end,
                ({
                    let iv = ItemTableInternalView::<I>{
                        row_info,
                        free_list: free_list@,
                        pending_allocations: Seq::<u64>::empty(),
                        pending_deallocations: Seq::<u64>::empty(),
                    };
                    &&& iv.consistent(*sm)
                    &&& iv.consistent_with_read_state(journal@.read_state, *sm)
                }),
                forall|any_row_addr: u64| {
                    &&& #[trigger] sm.table.validate_row_addr(any_row_addr)
                    &&& 0 <= sm.table.row_addr_to_index(any_row_addr) < row_index
                } ==> row_info.contains_key(any_row_addr),
                forall|any_row_addr: u64|
                    #[trigger] row_info.contains_key(any_row_addr) ==>
                    match row_info[any_row_addr] {
                        ItemRowDisposition::<I>::NowhereFree{ item } => item_addrs@.contains(any_row_addr),
                        ItemRowDisposition::<I>::InFreeList{ pos } => !item_addrs@.contains(any_row_addr),
                        _ => false,
                    },
                forall|i: int| 0 <= i < free_list@.len() ==>
                    0 <= sm.table.row_addr_to_index(#[trigger] free_list@[i]) < row_index,
            decreases
                sm.table.num_rows - row_index,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                sm.table.lemma_row_addr_successor_is_valid(row_addr);
            }

            let ghost old_free_list = free_list@;
            if !item_addrs.contains(&row_addr) {
                proof {
                    let ghost pos = free_list@.len();
                    row_info = row_info.insert(row_addr, ItemRowDisposition::InFreeList{ pos });
                }
                free_list.push(row_addr);
            }
            else {
                proof {
                    let ghost item = recover_item::<I>(journal@.read_state, row_addr, *sm);
                    row_info = row_info.insert(row_addr, ItemRowDisposition::NowhereFree{ item });
                }
            }

            row_index = row_index + 1;
            row_addr = row_addr + sm.table.row_size;
        }
    
        assert forall|row_addr: u64| #[trigger] sm.table.validate_row_addr(row_addr)
            implies row_info.contains_key(row_addr) by {
            let row_index = sm.table.row_addr_to_index(row_addr);
            broadcast use group_validate_row_addr;
        }

        let items = Self {
            status: Ghost(ItemTableStatus::Quiescent),
            sm: *sm,
            must_abort: Ghost(false),
            row_info: Ghost(row_info),
            free_list,
            pending_allocations: Vec::new(),
            pending_deallocations: Vec::new(),
            phantom_pm: Ghost(core::marker::PhantomData),
        };
        
        let ghost recovered_state = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
        assert(items@.durable =~= recovered_state);
        assert(items@.tentative == Some(recovered_state));
        assert(recovered_state.m.dom() =~= item_addrs@);

        proof {
            items.internal_view().lemma_corresponds_implication_for_free_list_length(*sm);
        }

        Ok(items)
    }
}

}
