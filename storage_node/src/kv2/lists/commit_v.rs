#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use super::{ListRowDisposition, ListSummary, ListTable, ListTableEntry, ListTableEntryView,
            ListTableInternalView, ListTableStaticMetadata};
use super::spec_v::*;
use super::super::spec_t::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn commit_m(self) -> Map<u64, ListTableEntryView<L>>
    {
        Map::<u64, ListTableEntryView<L>>::new(
            |list_addr: u64| self.m.contains_key(list_addr),
            |list_addr: u64| self.m[list_addr].commit(),
        )
    }

    pub(super) open spec fn commit_row_info(self) -> Map<u64, ListRowDisposition>
    {
        Map::<u64, ListRowDisposition>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64| match self.row_info[row_addr] {
                ListRowDisposition::InPendingAllocationList{ pos } =>
                    ListRowDisposition::NowhereFree,
                ListRowDisposition::InPendingDeallocationList{ pos } =>
                    ListRowDisposition::InFreeList{ pos: self.free_list.len() + pos },
                ListRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos } =>
                    ListRowDisposition::InFreeList{ pos: self.free_list.len() + dealloc_pos },
                _ => self.row_info[row_addr],
            },
        )
    }

    pub(super) open spec fn commit(self) -> Self
    {
        Self {
            durable_mapping: self.tentative_mapping,
            row_info: self.commit_row_info(),
            m: self.commit_m(),
            deletes_inverse: Map::<u64, nat>::empty(),
            deletes: Seq::<ListSummary>::empty(),
            modifications: Seq::<Option<u64>>::empty(),
            free_list: self.free_list + self.pending_deallocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
            ..self
        }
    }

    pub(super) proof fn lemma_commit_works(self, s: Seq<u8>, sm: ListTableStaticMetadata)
        requires
            self.valid(sm),
            self.corresponds_to_tentative_state(s, sm),
        ensures
            self.commit().valid(sm),
            self.commit().corresponds_to_durable_state(s, sm),
    {
    }
}

impl<L> ListTableEntry<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) exec fn commit(self) -> (result: Self)
        ensures
            result@ == self@.commit(),
            result@ == result@.commit(),
    {
        match self {
            ListTableEntry::Durable{ summary } => ListTableEntry::Durable{ summary },
            ListTableEntry::Modified{ summary, .. } => ListTableEntry::Durable{ summary },
        }
    }
}

impl<Perm, PM, L> ListTable<Perm, PM, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn update_m_to_reflect_commit_of_modifications(&mut self)
        requires
            forall|which_modification: int| 0 <= which_modification < old(self).modifications.len() ==>
                (#[trigger] old(self).modifications[which_modification] matches Some(list_addr) ==>
                 old(self).m@.contains_key(list_addr)),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| 0 <= i < self.modifications.len() ==>
                (#[trigger] old(self).modifications[i] matches Some(list_addr) ==> {
                    &&& self.m@.contains_key(list_addr)
                    &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                }),
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& {
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                   }
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
    {
        let num_modifications = self.modifications.len();
        for which_modification in 0..num_modifications
            invariant
                self == (Self{ m: self.m, ..*old(self) }),
                num_modifications == self.modifications.len(),
                forall|i: int| 0 <= i < old(self).modifications.len() ==>
                    (#[trigger] old(self).modifications[i] matches Some(list_addr) ==>
                     old(self).m@.contains_key(list_addr)),
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& {
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                       }
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
                forall|i: int| 0 <= i < which_modification ==>
                    (#[trigger] self.modifications[i] matches Some(list_addr) ==> {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& self.m@.contains_key(list_addr)
                        &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                        &&& self.m@[list_addr]@ == self.m@[list_addr]@.commit()
                    }),
        {
            broadcast use group_hash_axioms;
            match self.modifications[which_modification] {
                None => {},
                Some(list_addr) => {
                    let old_entry = self.m.remove(&list_addr);
                    assert(old_entry is Some);
                    let new_entry = old_entry.unwrap().commit();
                    self.m.insert(list_addr, new_entry);
                },
            };
        }
    }

    exec fn update_m_to_reflect_commit(&mut self, Ghost(jv): Ghost<JournalView>)
        requires
            old(self).valid(jv),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            self.internal_view().m == old(self).internal_view().commit().m,
    {
        self.update_m_to_reflect_commit_of_modifications();
        assert(self.internal_view().m =~= old(self).internal_view().commit().m);
    }

    pub exec fn commit(
        &mut self,
        Ghost(jv_before_commit): Ghost<JournalView>,
        Ghost(jv_after_commit): Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_commit),
            old(self)@.tentative is Some,
            jv_before_commit.valid(),
            jv_after_commit.valid(),
            jv_after_commit.committed_from(jv_before_commit),
        ensures
            self.valid(jv_after_commit),
            self@ == (ListTableView{ durable: old(self)@.tentative.unwrap(), used_slots: self@.used_slots, ..old(self)@ }),
            ({
                let m = self@.durable.m;
                &&& m.dom().finite()
                &&& self@.used_slots ==
                       m.dom().to_seq().fold_left(0, |total: int, row_addr: u64| total + m[row_addr].len())
            }),
    {
        let ghost new_iv = self.internal_view().commit();

        proof {
            self.internal_view().lemma_commit_works(jv_before_commit.commit_state, self.sm);
        }

        self.update_m_to_reflect_commit(Ghost(jv_before_commit));
        self.durable_mapping = self.tentative_mapping;
        self.deletes_inverse = Ghost(new_iv.deletes_inverse);
        self.deletes.clear();
        self.modifications.clear();
        self.row_info = Ghost(new_iv.row_info);
        self.free_list.append(&mut self.pending_deallocations);
        self.pending_allocations.clear();
        self.pending_deallocations.clear();

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;

        assert(self.internal_view() =~= old(self).internal_view().commit());

        assert(self.valid(jv_after_commit)) by {
            let jv_committed = JournalView{
                durable_state: jv_before_commit.commit_state,
                read_state: jv_before_commit.commit_state,
                commit_state: jv_before_commit.commit_state,
                remaining_capacity: jv_before_commit.constants.journal_capacity as int,
                journaled_addrs: Set::<int>::empty(),
                ..jv_before_commit
            };
            assert(self.valid(jv_committed));
            self.lemma_valid_depends_only_on_my_area(jv_committed, jv_after_commit);
        }

        proof {
            self.internal_view().lemma_corresponds_implication_for_free_list_length(self.sm);
        }

        assert(self@ =~= (ListTableView{ durable: old(self)@.tentative.unwrap(), used_slots: self@.used_slots,
                                         ..old(self)@ }));
    }
}

}

