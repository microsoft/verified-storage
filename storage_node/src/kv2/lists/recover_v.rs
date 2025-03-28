#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use super::impl_v::*;
use super::spec_v::*;
use super::super::spec_t::*;

verus! {

pub(super) struct ListRowRecoveryInfo<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub element: L,
    pub head: u64,
    pub next: u64,
    pub pos: int,
}

#[verifier::reject_recursive_types(L)]
#[verifier::ext_equal]
pub(super) struct ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub row_info: Map<u64, ListRowRecoveryInfo<L>>,
    pub list_info: Map<u64, Seq<u64>>,
    pub list_elements: Map<u64, Seq<L>>,
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
            list_elements: Map::<u64, Seq<L>>::empty(),
        }
    }
    
    pub(super) open spec fn row_info_corresponds(self, s: Seq<u8>, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==>
            {
                let row_info = self.row_info[row_addr];
                &&& recover_object::<u64>(s, row_addr + sm.row_next_start,
                                        row_addr + sm.row_next_start + u64::spec_size_of())
                    == Some(row_info.next)
                &&& recover_object::<L>(s, row_addr + sm.row_element_start, row_addr + sm.row_element_crc_start as int)
                    == Some(row_info.element)
            }
    }

    pub(super) open spec fn internally_consistent(self, sm: ListTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
               let row_info = self.row_info[row_addr];
               &&& sm.table.validate_row_addr(row_addr)
               &&& self.list_info.contains_key(row_info.head)
               &&& 0 <= row_info.pos < self.list_info[row_info.head].len()
               &&& self.list_info[row_info.head][row_info.pos as int] == row_addr
           }
        &&& forall|head: u64| #[trigger] self.list_info.contains_key(head) ==> {
               &&& 0 < self.list_info[head].len() <= usize::MAX
               &&& self.list_info[head][0] == head
               &&& self.list_elements.contains_key(head)
               &&& self.list_elements[head].len() == self.list_info[head].len()
           }
        &&& forall|head: u64| #[trigger] self.list_elements.contains_key(head) ==> self.list_info.contains_key(head)
        &&& forall|head: u64, pos: int| #![trigger self.list_info[head][pos]] {
               &&& self.list_info.contains_key(head)
               &&& 0 <= pos < self.list_info[head].len()
           } ==> {
               let info = self.row_info[self.list_info[head][pos]];
               &&& self.row_info.contains_key(self.list_info[head][pos])
               &&& info.head == head
               &&& info.pos == pos
               &&& info.next == 0 <==> pos == self.list_info[head].len() - 1
               &&& info.element == self.list_elements[head][pos]
           }
        &&& forall|head: u64, pos: int, successor: int| #![trigger self.list_info[head][pos], self.list_info[head][successor]] {
               &&& self.list_info.contains_key(head)
               &&& successor == pos + 1
               &&& 0 <= pos
               &&& successor < self.list_info[head].len()
           } ==> self.row_info[self.list_info[head][pos]].next == self.list_info[head][successor]
    }

    pub(super) open spec fn corresponds(self, s: Seq<u8>, list_addrs: Set<u64>, sm: ListTableStaticMetadata) -> bool
    {
        &&& self.internally_consistent(sm)
        &&& self.row_info_corresponds(s, sm)
        &&& self.list_elements.dom() == list_addrs
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
            0 <= pos < other.list_info[head].len(),
            pos == self.list_info[head].len() - 1 <==> pos == other.list_info[head].len() - 1,
            self.list_info[head][pos] == other.list_info[head][pos],
            self.list_elements[head][pos] == other.list_elements[head][pos],
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
            self.list_info[head][pos] == other.list_info[head][pos] by {
            self.lemma_uniqueness_element(other, s, list_addrs, sm, head, pos);
        }
        assert(other.list_info[head] =~= self.list_info[head]);
    }

    pub(super) proof fn lemma_uniqueness_elements(self, other: Self, s: Seq<u8>, list_addrs: Set<u64>,
                                                  sm: ListTableStaticMetadata, head: u64)
        requires
            sm.valid::<L>(),
            self.corresponds(s, list_addrs, sm),
            other.corresponds(s, list_addrs, sm),
            self.list_elements.contains_key(head),
        ensures
            other.list_elements.contains_key(head),
            other.list_elements[head] == self.list_elements[head],
    {
        self.lemma_uniqueness_length(other, s, list_addrs, sm, head);
        assert forall|pos: int| 0 <= pos < self.list_elements[head].len() implies
            self.list_elements[head][pos] == other.list_elements[head][pos] by {
            self.lemma_uniqueness_element(other, s, list_addrs, sm, head, pos);
        }
        assert(other.list_elements[head] =~= self.list_elements[head]);
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
        assert(self.list_elements =~= other.list_elements) by {
            assert forall|head: u64| #[trigger] self.list_elements.contains_key(head) implies {
                &&& other.list_elements.contains_key(head)
                &&& other.list_elements[head] == self.list_elements[head]
            } by {
                self.lemma_uniqueness_elements(other, s, list_addrs, sm, head);
            }
        }
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
        ListTableSnapshot::<L>{ m: self.list_elements }
    }
}

impl<Perm, PermFactory, PM, L> ListTable<Perm, PermFactory, PM, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub proof fn lemma_recover_depends_only_on_my_area_if_valid(
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
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        if Self::recover(s1, addrs, sm) is Some {
            Self::lemma_recover_depends_only_on_my_area_if_valid(s1, s2, addrs, sm);
        }
        else if Self::recover(s2, addrs, sm) is Some {
            Self::lemma_recover_depends_only_on_my_area_if_valid(s2, s1, addrs, sm);
        }
    }
}

}
