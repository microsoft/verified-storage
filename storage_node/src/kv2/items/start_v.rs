#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::super::impl_t::*;
use super::super::spec_t::*;
use super::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use deps_hack::PmCopy;
use recover_v::*;
use std::collections::HashSet;
use std::hash::Hash;

verus! {

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn start<K>(
        journal: &Journal<TrustedKvPermission, PM>,
        item_addrs: &HashSet<u64>,
        sm: &ItemTableStaticMetadata,
    ) -> (result: Result<Self, KvError<K>>)
        where
            K: std::fmt::Debug,
        requires
            journal.valid(),
            journal.recover_idempotent(),
            journal@.valid(),
            journal@.journaled_addrs == Set::<int>::empty(),
            journal@.durable_state == journal@.read_state,
            journal@.read_state == journal@.commit_state,
            Self::recover(journal@.read_state, item_addrs@, *sm) is Some,
            sm.valid::<I>(),
            sm.end() <= journal@.durable_state.len(),
        ensures
            match result {
                Ok(items) => {
                    let recovered_state = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
                    &&& items.valid(journal@)
                    &&& items@.sm == *sm
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

        let mut free_list: Vec<u64> = Vec::new();
        assert(free_list@.to_set().intersect(item_addrs@) == Set::<u64>::empty());

        let mut i = 0;
        while i < sm.table.num_rows
            invariant
                sm.table.valid(),
                // no addrs are in both the free list and item_addrs set
                free_list@.to_set().intersect(item_addrs@) == Set::<u64>::empty(),
                // for all rows between 0 and i, the corresponding address is
                // in one of the lists. this implies that rows without a
                // corresponding item_addr entry have been added to the free list
                forall |row: int| 0 <= row < i ==> {
                    let addr = #[trigger] sm.table.spec_row_index_to_addr(row);
                    ||| free_list@.contains(addr)
                    ||| item_addrs@.contains(addr)
                },
                // all addrs in the free list should be valid rows in the table
                forall |j: int| 0 <= j < free_list@.len() ==>
                    sm.table.validate_row_addr(#[trigger] free_list@[j]),
                // all items in item_addrs should be valid rows in the table
                forall |addr: u64| item_addrs@.contains(addr) ==>
                    sm.table.validate_row_addr(addr),
        {
            let ghost old_free_list = free_list@;
            let current_addr = sm.table.row_index_to_addr(i);

            if !item_addrs.contains(&current_addr) {
                free_list.push(current_addr);
            }

            proof {
                broadcast use vstd::std_specs::hash::group_hash_axioms;
                broadcast use group_validate_row_addr;

                lemma_row_index_to_addr_is_valid(sm.table, i as int);

                assert(old_free_list == free_list@.subrange(0, old_free_list.len() as int));
                assert(free_list@.to_set().intersect(item_addrs@) == Set::<u64>::empty());

                assert forall |row: int| 0 <= row <= i implies {
                    let addr = #[trigger] sm.table.spec_row_index_to_addr(row);
                    ||| free_list@.contains(addr)
                    ||| item_addrs@.contains(addr)
                } by {
                    let addr = sm.table.spec_row_index_to_addr(row);
                    if addr == current_addr {
                        if !item_addrs@.contains(addr) {
                            assert(free_list@.last() == addr);
                        }
                    }
                }
            }
            i += 1;
        }

        let ghost item_table_snapshot = Self::recover(journal@.read_state, item_addrs@, *sm).unwrap();
        let pending_deallocations = Vec::new();

        proof {
            broadcast use group_validate_row_addr;

            assert(item_table_snapshot.m.dom() == item_addrs@);
            assert(pending_deallocations@.to_set() == Set::<u64>::empty());
            assert(free_list@.to_set() + pending_deallocations@.to_set() == free_list@.to_set());
            assert(free_list@.to_set().intersect(pending_deallocations@.to_set()) == Set::<u64>::empty());

            assert(free_list@.to_set() + item_table_snapshot.m.dom() ==
                free_list@.to_set() + pending_deallocations@.to_set() + item_table_snapshot.m.dom());


            // making a sequence then a set is a little janky, but it's much easier than using Set::new and
            // trying to prove that the resulting set is finite
            let all_addrs_seq = Seq::new(sm.table.num_rows as nat, |i: int| sm.table.spec_row_index_to_addr(i));
            let all_addrs = all_addrs_seq.to_set();

            assert(free_list@.to_set() + item_addrs@ =~= all_addrs) by {
                // triggers?
                assert(forall |addr: u64| all_addrs.contains(addr) ==>
                    exists |row: int| sm.table.spec_row_index_to_addr(row) == addr);

                // TODO @hayley
                // i think this is true
                assert(forall |addr: u64| #[trigger] all_addrs.contains(addr) <==>
                    sm.table.validate_row_addr(addr));

                // assert forall |addr: u64| (free_list@.to_set() + item_addrs@).contains(addr) implies
                //     #[trigger] all_addrs.contains(addr)
                // by {
                //     // assert(sm.table.validate_row_addr(addr));
                // }

                // assert(forall |addr: u64| (free_list@.to_set() + item_addrs@).contains(addr) <==>
                //     #[trigger] all_addrs.contains(addr));
            }
        }

        Ok(Self {
            status: Ghost(ItemTableStatus::Quiescent),
            sm: *sm,
            must_abort: Ghost(false),
            durable_snapshot: Ghost(item_table_snapshot),
            tentative_snapshot: Ghost(item_table_snapshot),
            free_list,
            pending_deallocations,
            phantom_pm: Ghost(core::marker::PhantomData),
        })
    }
}

}
