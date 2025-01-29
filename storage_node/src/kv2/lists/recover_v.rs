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
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

pub(super) struct ListRowRecoveryInfo<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub element: L,
    pub head: u64,
    pub next: u64,
    pub pos: usize,
}

#[verifier::reject_recursive_types(L)]
#[verifier::ext_equal]
pub(super) struct ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub row_info: Map<u64, ListRowRecoveryInfo<L>>,
    pub list_info: Map<u64, Seq<u64>>,
}

impl<L> ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn new(s: Seq<u8>, list_addrs: Set<u64>, sm: ListTableStaticMetadata) -> Option<Self>
    {
        if exists|mapping: Self| mapping.corresponds(s, list_addrs, sm) {
            Some(choose|mapping: ListRecoveryMapping<L>| mapping.corresponds(s, list_addrs, sm))
        }
        else {
            None
        }
    }

    pub(super) open spec fn new_empty(tm: TableMetadata) -> Self
    {
        Self{
            row_info: Map::<u64, ListRowRecoveryInfo<L>>::empty(),
            list_info: Map::<u64, Seq<u64>>::empty(),
        }
    }
    
    pub(super) open spec fn row_info_corresponds(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==>
            {
                let row_info = self.row_info[row_addr];
                &&& sm.table.validate_row_addr(row_addr)
                &&& recover_object::<u64>(s, row_addr + sm.row_next_start, row_addr + sm.row_next_crc_start as int)
                    == Some(row_info.next)
                &&& recover_object::<L>(s, row_addr + sm.row_element_start, row_addr + sm.row_element_crc_start as int)
                    == Some(row_info.element)
                &&& self.list_info.contains_key(row_info.head)
                &&& row_info.pos < self.list_info[row_info.head].len()
                &&& self.list_info[row_info.head][row_info.pos as int] == row_addr
            }
    }

    pub(super) open spec fn list_info_corresponds(self, s: Seq<u8>, list_addrs: Set<u64>,
                                                  sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|head: u64| #[trigger] self.list_info.contains_key(head) ==>
        {
            &&& 0 < self.list_info[head].len()
            &&& self.list_info[head][0] == head
            &&& list_addrs.contains(head)
        }
        &&& forall|head: u64, pos: int| #![trigger self.list_info[head][pos]]
           {
               &&& self.list_info.contains_key(head)
               &&& 0 <= pos < self.list_info[head].len()
           } ==> {
               let info = self.row_info[self.list_info[head][pos as int]];
               &&& self.row_info.contains_key(self.list_info[head][pos as int])
               &&& info.head == head
               &&& info.pos == pos
               &&& info.next == 0 <==> pos == self.list_info[head].len() - 1
           }
        &&& forall|head: u64, pos: int, successor: int| #![trigger self.list_info[head][pos], self.list_info[head][successor]]
           {
               &&& self.list_info.contains_key(head)
               &&& successor == pos + 1
               &&& 0 <= pos
               &&& successor < self.list_info[head].len()
           } ==> self.row_info[self.list_info[head][pos]].next == self.list_info[head][successor]
        &&& forall|head: u64| #[trigger] list_addrs.contains(head) ==>
            self.list_info.contains_key(head)
    }

    pub(super) open spec fn corresponds(self, s: Seq<u8>, list_addrs: Set<u64>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.row_info_corresponds(s, sm)
        &&& self.list_info_corresponds(s, list_addrs, sm)
    }

    pub(super) proof fn lemma_uniqueness_element(self, other: Self, s: Seq<u8>, list_addrs: Set<u64>,
                                                 sm: ListTableStaticMetadata, head: u64, pos: int)
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
            other.corresponds(s, list_addrs, sm),
            self.list_info.contains_key(head),
            0 <= pos < self.list_info[head].len(),
        ensures
            pos < other.list_info[head].len(),
            pos == self.list_info[head].len() - 1 <==> pos == other.list_info[head].len() - 1,
            self.list_info[head][pos] == other.list_info[head][pos],
        decreases
            pos,
    {
        if pos > 0 {
            self.lemma_uniqueness_element(other, s, list_addrs, sm, head, pos - 1);
            assert(self.row_info[self.list_info[head][pos]] =~= other.row_info[other.list_info[head][pos]]);
        }
    }

    pub(super) proof fn lemma_uniqueness_length(self, other: Self, s: Seq<u8>, list_addrs: Set<u64>,
                                                sm: ListTableStaticMetadata, head: u64)
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
            other.corresponds(s, list_addrs, sm),
            self.list_info.contains_key(head),
        ensures
            self.list_info[head].len() == other.list_info[head].len(),
    {
        self.lemma_uniqueness_element(other, s, list_addrs, sm, head, self.list_info[head].len() - 1);
    }

    pub(super) proof fn lemma_uniqueness_list(self, other: Self, s: Seq<u8>, list_addrs: Set<u64>,
                                              sm: ListTableStaticMetadata, head: u64)
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
            other.corresponds(s, list_addrs, sm),
            self.list_info.contains_key(head),
        ensures
            other.list_info.contains_key(head),
            other.list_info[head] == self.list_info[head],
    {
        self.lemma_uniqueness_length(other, s, list_addrs, sm, head);
        assert forall|pos: int| 0 <= pos < self.list_info[head].len() implies
            self.list_info[head][pos as int] == other.list_info[head][pos as int] by {
            self.lemma_uniqueness_element(other, s, list_addrs, sm, head, pos);
        }
        assert(other.list_info[head] =~= self.list_info[head]);
    }

    pub(super) proof fn lemma_uniqueness(self, other: Self, s: Seq<u8>, list_addrs: Set<u64>,
                                         sm: ListTableStaticMetadata)
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
            other.corresponds(s, list_addrs, sm),
        ensures
            self == other,
    {
        assert(self.list_info =~= other.list_info) by {
            assert forall|head: u64| #[trigger] self.list_info.contains_key(head) implies {
                &&& other.list_info.contains_key(head)
                &&& other.list_info[head] == self.list_info[head]
            } by {
                self.lemma_uniqueness_list(other, s, list_addrs, sm, head);
            }
        }
        assert(self.row_info =~= other.row_info);
        assert(self =~= other);
    }

    pub(super) proof fn lemma_corresponds_implies_equals_new(
        self,
        s: Seq<u8>,
        list_addrs: Set<u64>,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
        ensures
            Self::new(s, list_addrs, sm) == Some(self),
    {
        self.lemma_uniqueness(Self::new(s, list_addrs, sm).unwrap(), s, list_addrs, sm);
    }

    pub(super) open spec fn as_snapshot(self: ListRecoveryMapping<L>) -> ListTableSnapshot<L>
    {
        ListTableSnapshot::<L>{
            m: Map::<u64, Seq<L>>::new(
                |list_addr: u64| self.list_info.contains_key(list_addr),
                |list_addr: u64| self.list_info[list_addr].map(|_i, row_addr: u64| self.row_info[row_addr].element),
            ),
        }
    }
    
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        addrs: Set<u64>,
        sm: ListTableStaticMetadata,
    )
        requires
            sm.valid::<L>(),
            sm.end() <= s1.len(),
            seqs_match_in_range(s1, s2, sm.start() as int, sm.end() as int),
            Self::recover(s1, addrs, sm) is Some,
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        let mapping1 = ListRecoveryMapping::<L>::new(s1, addrs, sm).unwrap();
        assert(mapping1.corresponds(s2, addrs, sm)) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            broadcast use group_validate_row_addr;
        }
        mapping1.lemma_corresponds_implies_equals_new(s2, addrs, sm);
    }
}

}
