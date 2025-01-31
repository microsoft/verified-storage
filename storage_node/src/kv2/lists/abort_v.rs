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
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::std_specs::hash::*;

verus! {

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn abort_m(self) -> Map<u64, ListTableEntryView<L>>
    {
        Map::<u64, ListTableEntryView<L>>::new(
            |list_addr: u64| {
                ||| self.deletes_inverse.contains_key(list_addr)
                ||| {
                       &&& self.m.contains_key(list_addr)
                       &&& self.m[list_addr] is Durable
                   }
            },
            |list_addr: u64| {
                if self.deletes_inverse.contains_key(list_addr) {
                    ListTableEntryView::Durable{ entry: self.deletes[self.deletes_inverse[list_addr] as int] }
                }
                else {
                    self.m[list_addr]
                }
            }
        )
    }

    pub(super) open spec fn abort_row_info(self) -> Map<u64, ListRowDisposition<L>>
    {
        Map::<u64, ListRowDisposition<L>>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64| match self.row_info[row_addr] {
                ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + pos },
                ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                    ListRowDisposition::<L>::NowhereFree{ element },
                ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + alloc_pos },
                _ => self.row_info[row_addr],
            },
        )
    }

    pub(super) open spec fn abort(self) -> Self
    {
        Self {
            durable_list_addrs: self.durable_list_addrs,
            tentative_list_addrs: self.durable_list_addrs,
            durable_mapping: self.durable_mapping,
            tentative_mapping: self.durable_mapping,
            row_info: self.abort_row_info(),
            m: self.abort_m(),
            deletes_inverse: Map::<u64, usize>::empty(),
            deletes: Seq::<ListTableDurableEntry>::empty(),
            updates: Seq::<Option<u64>>::empty(),
            creates: Seq::<Option<u64>>::empty(),
            free_list: self.free_list + self.pending_allocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
        }
    }

    pub(super) proof fn lemma_abort_works(self, s: Seq<u8>, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
            self.corresponds_to_durable_state(s, sm),
        ensures
            self.abort().valid(sm),
            self.abort().corresponds_to_durable_state(s, sm),
    {
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn update_m_to_reflect_abort_of_updates(&mut self)
        requires
            forall|i: int| 0 <= i < old(self).updates.len() ==>
                match #[trigger] old(self).updates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& old(self).m@[list_addr] is Updated
                    },
                },
            forall|i: int| 0 <= i < old(self).creates.len() ==>
                match #[trigger] old(self).creates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& old(self).m@[list_addr] is Created
                    },
                },
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| 0 <= i < self.updates.len() ==>
                match #[trigger] old(self).updates[i] {
                    None => true,
                    Some(list_addr) => !self.m@.contains_key(list_addr),
                },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==>
                (old(self).m[list_addr] is Durable ==> self.m@.contains_key(list_addr)),
            forall|i: int| 0 <= i < self.creates.len() ==>
                match #[trigger] self.creates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& self.m@.contains_key(list_addr)
                        &&& self.m@[list_addr] is Created
                    },
                },
    {
        let mut which_update = 0;
        let num_updates = self.updates.len();

        while which_update < num_updates
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                0 <= which_update <= num_updates,
                num_updates == self.updates.len(),
                forall|i: int| 0 <= i < old(self).updates.len() ==>
                    match #[trigger] old(self).updates[i] {
                        None => true,
                        Some(list_addr) => {
                            &&& old(self).m@.contains_key(list_addr)
                            &&& old(self).m@[list_addr] is Updated
                        },
                    },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==>
                    (old(self).m[list_addr] is Durable ==> self.m@.contains_key(list_addr)),
                forall|i: int| 0 <= i < which_update ==>
                    match #[trigger] self.updates[i] {
                        None => true,
                        Some(list_addr) => !self.m@.contains_key(list_addr),
                    },
                forall|i: int| 0 <= i < self.creates.len() ==>
                    match #[trigger] self.creates[i] {
                        None => true,
                        Some(list_addr) => {
                            &&& self.m@.contains_key(list_addr)
                            &&& self.m@[list_addr] is Created
                        },
                    },
        {
            broadcast use group_hash_axioms;
            match self.updates[which_update] {
                None => {},
                Some(list_addr) => { self.m.remove(&list_addr); },
            };
            which_update += 1;
        }
    }

    exec fn update_m_to_reflect_abort_of_creates(&mut self)
        requires
            forall|i: int| 0 <= i < old(self).creates.len() ==>
                match #[trigger] old(self).creates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& old(self).m@[list_addr] is Created
                    },
                },
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| 0 <= i < self.creates.len() ==>
                match #[trigger] old(self).creates[i] {
                    None => true,
                    Some(list_addr) => !self.m@.contains_key(list_addr),
                },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==>
                (old(self).m[list_addr] is Durable ==> self.m@.contains_key(list_addr)),
    {
        let mut which_create = 0;
        let num_creates = self.creates.len();

        while which_create < num_creates
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                0 <= which_create <= num_creates,
                num_creates == self.creates.len(),
                forall|i: int| 0 <= i < old(self).creates.len() ==>
                    match #[trigger] old(self).creates[i] {
                        None => true,
                        Some(list_addr) => {
                            &&& old(self).m@.contains_key(list_addr)
                            &&& old(self).m@[list_addr] is Created
                        },
                    },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==>
                    (old(self).m[list_addr] is Durable ==> self.m@.contains_key(list_addr)),
                forall|i: int| 0 <= i < which_create ==>
                    match #[trigger] self.creates[i] {
                        None => true,
                        Some(list_addr) => !self.m@.contains_key(list_addr),
                    },
        {
            broadcast use group_hash_axioms;
            match self.creates[which_create] {
                None => {},
                Some(list_addr) => { self.m.remove(&list_addr); },
            };
            which_create += 1;
        }
    }

    exec fn update_m_to_reflect_abort_of_deletes(&mut self)
        requires
            forall|list_addr: u64| #[trigger] old(self).internal_view().deletes_inverse.contains_key(list_addr) ==> {
                let which_delete = old(self).internal_view().deletes_inverse[list_addr];
                &&& 0 <= which_delete < old(self).internal_view().deletes.len()
                &&& old(self).internal_view().deletes[which_delete as int].head == list_addr
            },
            forall|i: int| #![trigger old(self).internal_view().deletes[i]]
                0 <= i < old(self).internal_view().deletes.len() ==> {
                    let entry = old(self).internal_view().deletes[i];
                    &&& old(self).internal_view().deletes_inverse.contains_key(entry.head)
                    &&& old(self).internal_view().deletes_inverse[entry.head] == i
                },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> old(self).m@[list_addr] is Durable,
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| #![trigger self.deletes[i]] 0 <= i < self.deletes.len() ==> {
                let entry = self.deletes[i];
                &&& self.m@.contains_key(entry.head)
                &&& self.m@[entry.head] == ListTableEntry::<L>::Durable{ entry }
            },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                if self.deletes_inverse@.contains_key(list_addr) {
                    let entry = self.deletes@[self.deletes_inverse@[list_addr] as int];
                    &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{ entry }
                }
                else {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                }
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> {
                ||| {
                       &&& old(self).deletes_inverse@.contains_key(list_addr)
                       &&& self.m@.contains_key(list_addr)
                       &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{
                           entry: self.deletes@[self.deletes_inverse@[list_addr] as int]
                       }
                    }
                ||| {
                       &&& self.m@.contains_key(list_addr)
                       &&& self.m@[list_addr] == old(self).m@[list_addr]
                   }
            },
    {
        let mut which_delete = 0;
        let num_deletes = self.deletes.len();

        while which_delete < num_deletes
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                0 <= which_delete <= num_deletes,
                num_deletes == self.deletes.len(),
                forall|list_addr: u64| #[trigger] self.internal_view().deletes_inverse.contains_key(list_addr) ==> {
                    let which_delete = self.internal_view().deletes_inverse[list_addr];
                    &&& 0 <= which_delete < self.internal_view().deletes.len()
                    &&& self.internal_view().deletes[which_delete as int].head == list_addr
                },
                forall|i: int| #![trigger self.internal_view().deletes[i]]
                    0 <= i < self.internal_view().deletes.len() ==> {
                        let entry = self.internal_view().deletes[i];
                        &&& self.internal_view().deletes_inverse.contains_key(entry.head)
                        &&& self.internal_view().deletes_inverse[entry.head] == i
                    },
                forall|i: int| #![trigger self.deletes[i]] 0 <= i < which_delete ==> {
                    let entry = self.deletes[i];
                    &&& self.m@.contains_key(entry.head)
                    &&& self.m@[entry.head] == ListTableEntry::<L>::Durable{ entry }
                },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> self.m@[list_addr] is Durable,
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    ||| {
                        &&& self.internal_view().deletes_inverse.contains_key(list_addr)
                        &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{
                            entry: self.deletes@[self.internal_view().deletes_inverse[list_addr] as int]
                        }
                    }
                    ||| {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                    }
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> {
                    ||| {
                           &&& old(self).deletes_inverse@.contains_key(list_addr)
                           &&& self.m@.contains_key(list_addr)
                           &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{
                               entry: self.deletes@[self.deletes_inverse@[list_addr] as int]
                           }
                        }
                    ||| {
                           &&& self.m@.contains_key(list_addr)
                           &&& self.m@[list_addr] == old(self).m@[list_addr]
                       }
            },
        {
            broadcast use group_hash_axioms;
            let ghost prev_self = *self;
            let entry = self.deletes[which_delete].clone();
            assert(entry == self.deletes[which_delete as int]);
            self.m.insert(entry.head, ListTableEntry::<L>::Durable{ entry });
            assert(self.internal_view().deletes_inverse == prev_self.internal_view().deletes_inverse);
            assert(self.internal_view().deletes == prev_self.internal_view().deletes);
            which_delete += 1;
        }

        assert forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) implies {
                if self.deletes_inverse@.contains_key(list_addr) {
                    let entry = self.deletes@[self.deletes_inverse@[list_addr] as int];
                    &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{ entry }
                }
                else {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                }
            } by {
            if self.deletes_inverse@.contains_key(list_addr) {
                assert(self.internal_view().deletes_inverse.contains_key(list_addr));
            }
        }
    }

    exec fn update_m_to_reflect_abort(&mut self, Ghost(jv): Ghost<JournalView>)
        requires
            old(self).valid(jv),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            self.internal_view().m == old(self).internal_view().abort().m,
    {
        self.update_m_to_reflect_abort_of_updates();

        assert forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) implies !(self.m@[list_addr] is Updated)
        by {
            assert(old(self).internal_view().m.contains_key(list_addr));
        }

        self.update_m_to_reflect_abort_of_creates();

        assert forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) implies !(self.m@[list_addr] is Created)
        by {
            assert(old(self).internal_view().m.contains_key(list_addr));
        }

        assert(self.internal_view().deletes_inverse == old(self).internal_view().deletes_inverse);
        assert(self.internal_view().deletes == old(self).internal_view().deletes);
        assert(self.internal_view().deletes_inverse_is_inverse_of_deletes());
        
        self.update_m_to_reflect_abort_of_deletes();

        proof {
            let m1 = self.internal_view().m;
            let m2 = old(self).internal_view().abort().m;
            assert(forall|list_addr: u64| m2.contains_key(list_addr) ==> m1.contains_key(list_addr));
            assert(forall|list_addr: u64| m1.contains_key(list_addr) ==> m2.contains_key(list_addr));
        }
        
        assert(self.internal_view().m =~= old(self).internal_view().abort().m);
    }
    
    pub exec fn abort(
        &mut self,
        Ghost(jv_before_abort): Ghost<JournalView>,
        Ghost(jv_after_abort): Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_abort),
            jv_before_abort.valid(),
            jv_after_abort.valid(),
            jv_after_abort == jv_before_abort.abort(),
        ensures
            self.valid(jv_after_abort),
            self@ == (ListTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }),
    {
        let ghost new_iv = self.internal_view().abort();

        proof {
            self.internal_view().lemma_abort_works(jv_before_abort.durable_state, self.sm);
        }

        self.update_m_to_reflect_abort(Ghost(jv_before_abort));
        self.tentative_list_addrs = self.durable_list_addrs;
        self.tentative_mapping = self.durable_mapping;
        self.deletes_inverse = Ghost(new_iv.deletes_inverse);
        self.deletes.clear();
        self.updates.clear();
        self.creates.clear();
        self.row_info = Ghost(new_iv.row_info);
        self.free_list.append(&mut self.pending_allocations);
        self.pending_allocations.clear();
        self.pending_deallocations.clear();
        self.must_abort = Ghost(false);

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(self.internal_view() =~= old(self).internal_view().abort());

        assert(self.valid(jv_after_abort));
        assert(self@ =~= (ListTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }));
    }
}

}

