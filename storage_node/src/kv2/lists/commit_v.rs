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
    pub(super) open spec fn commit_m(self) -> Map<u64, ListTableEntryView<L>>
    {
        Map::<u64, ListTableEntryView<L>>::new(
            |list_addr: u64| self.m.contains_key(list_addr),
            |list_addr: u64| self.m[list_addr].commit(),
        )
    }

    pub(super) open spec fn commit_row_info(self) -> Map<u64, ListRowDisposition<L>>
    {
        Map::<u64, ListRowDisposition<L>>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64| match self.row_info[row_addr] {
                ListRowDisposition::<L>::InPendingAllocationList{ pos, element } =>
                    ListRowDisposition::<L>::NowhereFree{ element },
                ListRowDisposition::<L>::InPendingDeallocationList{ pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + pos },
                ListRowDisposition::<L>::InBothPendingLists{ alloc_pos, dealloc_pos, element } =>
                    ListRowDisposition::<L>::InFreeList{ pos: self.free_list.len() + dealloc_pos },
                _ => self.row_info[row_addr],
            },
        )
    }

    pub(super) open spec fn commit(self) -> Self
    {
        Self {
            durable_list_addrs: self.tentative_list_addrs,
            tentative_list_addrs: self.tentative_list_addrs,
            durable_mapping: self.tentative_mapping,
            tentative_mapping: self.tentative_mapping,
            row_info: self.commit_row_info(),
            m: self.commit_m(),
            deletions_inverse: Map::<u64, usize>::empty(),
            deletions: Seq::<ListTableDurableEntry>::empty(),
            updates: Seq::<Option<u64>>::empty(),
            creates: Seq::<Option<u64>>::empty(),
            free_list: self.free_list + self.pending_deallocations,
            pending_allocations: Seq::<u64>::empty(),
            pending_deallocations: Seq::<u64>::empty(),
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
        requires
            self matches ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } ==> {
                &&& 0 < tentative_addrs.len()
                &&& tentative_addrs.len() == tentative_elements.len()
            },
        ensures
            result@ == self@.commit(),
            result@ == result@.commit(),
    {
        match self {
            ListTableEntry::Durable{ entry } => ListTableEntry::Durable{ entry },
            ListTableEntry::Updated{ tentative, .. } => ListTableEntry::Durable{ entry: tentative },
            ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } => {
                let last_pos = tentative_addrs.len() - 1;
                ListTableEntry::Durable{
                    entry: ListTableDurableEntry{
                        head: tentative_addrs[0],
                        tail: tentative_addrs[last_pos],
                        length: tentative_addrs.len(),
                        end_of_logical_range: tentative_elements[last_pos].end(),
                    }
                }
            }
        }
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn update_m_to_reflect_commit_of_updates(&mut self)
        requires
            forall|which_update: int| 0 <= which_update < old(self).updates.len() ==>
                match #[trigger] old(self).updates[which_update] {
                    None => true,
                    Some(list_addr) => {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& (old(self).m@[list_addr] matches
                            ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } ==> {
                                &&& 0 < tentative_addrs.len()
                                &&& tentative_addrs.len() == tentative_elements.len()
                            })
                    },
                },
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| 0 <= i < self.updates.len() ==>
                match #[trigger] old(self).updates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& self.m@.contains_key(list_addr)
                        &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                    }
                },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& {
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                   }
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
    {
        broadcast use group_hash_axioms;

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
                            &&& (old(self).m@[list_addr] matches
                                ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } ==> {
                                    &&& 0 < tentative_addrs.len()
                                    &&& tentative_addrs.len() == tentative_elements.len()
                                })
                        },
                    },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& {
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                       }
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
                forall|i: int| 0 <= i < which_update ==>
                    match #[trigger] self.updates[i] {
                        None => true,
                        Some(list_addr) => {
                            &&& old(self).m@.contains_key(list_addr)
                            &&& self.m@.contains_key(list_addr)
                            &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                            &&& self.m@[list_addr]@ == self.m@[list_addr]@.commit()
                        }
                    },
        {
            broadcast use group_hash_axioms;
            match self.updates[which_update] {
                None => {},
                Some(list_addr) => {
                    let old_entry = self.m.remove(&list_addr);
                    assert(old_entry is Some);
                    let new_entry = old_entry.unwrap().commit();
                    self.m.insert(list_addr, new_entry);
                },
            };
            which_update += 1;
        }
    }

    exec fn update_m_to_reflect_commit_of_creates(&mut self)
        requires
            forall|which_create: int| 0 <= which_create < old(self).creates.len() ==>
                match #[trigger] old(self).creates[which_create] {
                    None => true,
                    Some(list_addr) => {
                        &&& old(self).m@.contains_key(list_addr)
                        &&& (old(self).m@[list_addr] matches
                            ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } ==> {
                                &&& 0 < tentative_addrs.len()
                                &&& tentative_addrs.len() == tentative_elements.len()
                            })
                    },
                },
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            forall|i: int| 0 <= i < self.creates.len() ==>
                match #[trigger] old(self).creates[i] {
                    None => true,
                    Some(list_addr) => {
                        &&& self.m@.contains_key(list_addr)
                        &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                    }
                },
            forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                &&& old(self).m@.contains_key(list_addr)
                &&& {
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                       ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                   }
            },
            forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
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
                            &&& (old(self).m@[list_addr] matches
                                ListTableEntry::Created{ tentative_addrs, tentative_elements, .. } ==> {
                                    &&& 0 < tentative_addrs.len()
                                    &&& tentative_addrs.len() == tentative_elements.len()
                                })
                        },
                    },
                forall|list_addr: u64| #[trigger] self.m@.contains_key(list_addr) ==> {
                    &&& old(self).m@.contains_key(list_addr)
                    &&& {
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@
                           ||| self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                       }
                },
                forall|list_addr: u64| #[trigger] old(self).m@.contains_key(list_addr) ==> self.m@.contains_key(list_addr),
                forall|i: int| 0 <= i < which_create ==>
                    match #[trigger] self.creates[i] {
                        None => true,
                        Some(list_addr) => {
                            &&& old(self).m@.contains_key(list_addr)
                            &&& self.m@.contains_key(list_addr)
                            &&& self.m@[list_addr]@ == old(self).m@[list_addr]@.commit()
                            &&& self.m@[list_addr]@ == self.m@[list_addr]@.commit()
                        }
                    },
        {
            broadcast use group_hash_axioms;
            match self.creates[which_create] {
                None => {},
                Some(list_addr) => {
                    let old_entry = self.m.remove(&list_addr);
                    assert(old_entry is Some);
                    let new_entry = old_entry.unwrap().commit();
                    self.m.insert(list_addr, new_entry);
                },
            };
            which_create += 1;
        }
    }

    exec fn update_m_to_reflect_commit(&mut self, Ghost(jv): Ghost<JournalView>)
        requires
            old(self).valid(jv),
        ensures
            self == (Self{ m: self.m, ..*old(self) }),
            self.internal_view().m == old(self).internal_view().commit().m,
    {
        self.update_m_to_reflect_commit_of_updates();
        self.update_m_to_reflect_commit_of_creates();
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
            self@ == (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }),
    {
        let ghost new_iv = self.internal_view().commit();

        proof {
            self.internal_view().lemma_commit_works(jv_before_commit.commit_state, self.sm);
        }

        self.update_m_to_reflect_commit(Ghost(jv_before_commit));
        self.durable_list_addrs = self.tentative_list_addrs;
        self.durable_mapping = self.tentative_mapping;
        self.deletions_inverse = Ghost(new_iv.deletions_inverse);
        self.deletions.clear();
        self.updates.clear();
        self.creates.clear();
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
        assert(self@ =~= (ListTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }));
    }
}

}

