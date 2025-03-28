#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use super::impl_v::*;
use super::inv_v::*;
use super::spec_v::*;
use super::super::spec_t::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {

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
                    ListTableEntryView::Durable{ summary: self.deletes[self.deletes_inverse[list_addr] as int] }
                }
                else {
                    self.m[list_addr]
                }
            }
        )
    }

    pub(super) open spec fn abort_row_info(self) -> Map<u64, ListRowDisposition>
    {
        Map::<u64, ListRowDisposition>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64| match self.row_info[row_addr] {
                ListRowDisposition::InPendingAllocationList{ pos } =>
                    ListRowDisposition::InFreeList{ pos: self.free_list.len() + pos },
                ListRowDisposition::InPendingDeallocationList{ pos } =>
                    ListRowDisposition::NowhereFree,
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } =>
                    ListRowDisposition::InFreeList{ pos: self.free_list.len() + alloc_pos },
                _ => self.row_info[row_addr],
            },
        )
    }

    pub(super) open spec fn abort(self) -> Self
    {
        Self {
            tentative_mapping: self.durable_mapping,
            row_info: self.abort_row_info(),
            m: self.abort_m(),
            deletes_inverse: Map::<u64, nat>::empty(),
            deletes: Seq::<ListSummary>::empty(),
            modifications: Seq::<Option<u64>>::empty(),
            free_list: self.free_list + self.pending_allocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
            ..self
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

impl<Perm, PermFactory, PM, L> ListTable<Perm, PermFactory, PM, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn update_m_to_reflect_abort_of_modifications(&mut self)
        requires
            forall|i: int| 0 <= i < old(self).modifications.len() ==>
                (#[trigger] old(self).modifications[i] matches Some(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& !(old(self).m@[list_addr] is Durable)
                }),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            self.internal_view() == (ListTableInternalView{ m: self.internal_view().m, ..old(self).internal_view() }),
            forall|i: int| 0 <= i < self.modifications.len() ==>
                (#[trigger] old(self).modifications[i] matches Some(list_addr) ==> !self.m@.contains_key(list_addr)),
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
            },
            forall|list_addr: u64| {
                &&& #[trigger] old(self).m@.contains_key(list_addr)
                &&& old(self).m[list_addr] is Durable
            } ==> self.m@.contains_key(list_addr),
    {
        let num_modifications = self.modifications.len();

        for which_modification in 0..num_modifications
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                num_modifications == self.modifications.len(),
                forall|i: int| 0 <= i < old(self).modifications.len() ==>
                    (#[trigger] old(self).modifications[i] matches Some(list_addr) ==> {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& !(old(self).m@[list_addr] is Durable)
                    }),
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@
                },
                forall|list_addr: u64| {
                    &&& #[trigger] old(self).m@.contains_key(list_addr)
                    &&& old(self).m[list_addr] is Durable
                } ==> self.m@.contains_key(list_addr),
                forall|i: int| 0 <= i < which_modification ==>
                    (#[trigger] self.modifications[i] matches Some(list_addr) ==> !self.m@.contains_key(list_addr)),
        {
            broadcast use group_hash_axioms;
            match self.modifications[which_modification] {
                None => {},
                Some(list_addr) => { self.m.remove(&list_addr); },
            };
        }
    }

    exec fn update_m_to_reflect_abort_of_deletes(&mut self)
        requires
            forall|list_addr: u64| #[trigger] old(self).deletes_inverse@.contains_key(list_addr) ==> {
                let which_delete = old(self).deletes_inverse@[list_addr];
                &&& 0 <= which_delete < old(self).deletes@.len()
                &&& old(self).deletes@[which_delete as int].head == list_addr
            },
            forall|i: int| #![trigger old(self).deletes@[i]]
                0 <= i < old(self).deletes@.len() ==> {
                    let summary = old(self).deletes@[i];
                    &&& old(self).deletes_inverse@.contains_key(summary.head)
                    &&& old(self).deletes_inverse@[summary.head] == i
                },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> old(self).m@[list_addr] is Durable,
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| #![trigger self.deletes[i]] 0 <= i < self.deletes.len() ==> {
                let summary = self.deletes[i];
                &&& self.m@.contains_key(summary.head)
                &&& self.m@[summary.head] == ListTableEntry::<L>::Durable{ summary }
            },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                if self.deletes_inverse@.contains_key(list_addr) {
                    let summary = self.deletes@[self.deletes_inverse@[list_addr] as int];
                    &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{ summary }
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
                           summary: self.deletes@[self.deletes_inverse@[list_addr] as int]
                       }
                    }
                ||| {
                       &&& self.m@.contains_key(list_addr)
                       &&& self.m@[list_addr] == old(self).m@[list_addr]
                   }
            },
    {
        let num_deletes = self.deletes.len();

        for which_delete in 0..num_deletes
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                num_deletes == self.deletes.len(),
                forall|list_addr: u64| #[trigger] self.deletes_inverse@.contains_key(list_addr) ==> {
                    let which_delete = self.deletes_inverse@[list_addr];
                    &&& 0 <= which_delete < self.deletes@.len()
                    &&& self.deletes@[which_delete as int].head == list_addr
                },
                forall|i: int| #![trigger self.deletes@[i]]
                    0 <= i < self.deletes@.len() ==> {
                        let summary = self.deletes@[i];
                        &&& self.deletes_inverse@.contains_key(summary.head)
                        &&& self.deletes_inverse@[summary.head] == i
                    },
                forall|i: int| #![trigger self.deletes[i]] 0 <= i < which_delete ==> {
                    let summary = self.deletes[i];
                    &&& self.m@.contains_key(summary.head)
                    &&& self.m@[summary.head] == ListTableEntry::<L>::Durable{ summary }
                },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> self.m@[list_addr] is Durable,
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    ||| {
                        &&& self.deletes_inverse@.contains_key(list_addr)
                        &&& self.m@[list_addr] == ListTableEntry::<L>::Durable{
                            summary: self.deletes@[self.deletes_inverse@[list_addr] as int]
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
                               summary: self.deletes@[self.deletes_inverse@[list_addr] as int]
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
            let summary = self.deletes[which_delete];
            self.m.insert(summary.head, ListTableEntry::<L>::Durable{ summary });
        }
    }

    exec fn update_m_to_reflect_abort(&mut self, Ghost(jv): Ghost<JournalView>)
        requires
            old(self).valid(jv),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            self.internal_view().m == old(self).internal_view().abort().m,
    {
        self.update_m_to_reflect_abort_of_modifications();

        assert forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) implies self.m@[list_addr] is Durable
        by {
            assert(old(self).internal_view().m.contains_key(list_addr));
        }
        
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
            self@ == (ListTableView{ tentative: Some(old(self)@.durable), used_slots: self@.used_slots, ..old(self)@ }),
            ({
                let m = self@.durable.m;
                &&& m.dom().finite()
                &&& self@.used_slots ==
                       m.dom().to_seq().fold_left(0, |total: int, row_addr: u64| total + m[row_addr].len())
            }),
    {
        let ghost new_iv = self.internal_view().abort();

        proof {
            self.internal_view().lemma_abort_works(jv_before_abort.durable_state, self.sm);
        }

        self.update_m_to_reflect_abort(Ghost(jv_before_abort));
        self.tentative_mapping = self.durable_mapping;
        self.deletes_inverse = Ghost(new_iv.deletes_inverse);
        self.deletes.clear();
        self.modifications.clear();
        self.row_info = Ghost(new_iv.row_info);
        self.free_list.append(&mut self.pending_allocations);
        self.pending_allocations.clear();
        self.pending_deallocations.clear();
        self.must_abort = Ghost(false);

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(self.internal_view() =~= old(self).internal_view().abort());

        assert(self.valid(jv_after_abort));

        proof {
            self.internal_view().lemma_corresponds_implication_for_free_list_length(self.sm);
        }

        assert(self@ =~= (ListTableView{ tentative: Some(old(self)@.durable), used_slots: self@.used_slots,
                                         ..old(self)@ }));
    }
}

}

