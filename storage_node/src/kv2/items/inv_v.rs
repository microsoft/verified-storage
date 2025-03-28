#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
use crate::journal::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::wrpm_t::*;
use super::{ItemTable, ItemTableSnapshot, ItemTableStaticMetadata};

verus! {

#[verifier::ext_equal]
pub(super) enum ItemTableStatus {
    Quiescent,
}

#[verifier::ext_equal]
pub(super) enum ItemRowDisposition<I>
    where
        I: PmCopy + Sized + std::fmt::Debug,
{
    NowhereFree{ item: I },
    InFreeList{ pos: nat },
    InPendingDeallocationList{ pos: nat, item: I },
    InPendingAllocationList{ pos: nat, item: I },
    InBothPendingLists{ alloc_pos: nat, dealloc_pos: nat, item: I },
}

#[verifier::ext_equal]
pub(super) struct ItemTableInternalView<I>
    where
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub row_info: Map<u64, ItemRowDisposition<I>>,
    pub free_list: Seq<u64>,
    pub pending_allocations: Seq<u64>,
    pub pending_deallocations: Seq<u64>,
}

impl<I> ItemTableInternalView<I>
    where
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub(super) open spec fn complete(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] sm.table.validate_row_addr(row_addr) ==> self.row_info.contains_key(row_addr)
    }

    pub(super) open spec fn row_info_consistent(self, sm: ItemTableStaticMetadata) -> bool
    {
        forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            &&& sm.table.validate_row_addr(row_addr)
            &&& match self.row_info[row_addr] {
                  ItemRowDisposition::NowhereFree{ item } => true,
                  ItemRowDisposition::InFreeList{ pos } => {
                      &&& 0 <= pos < self.free_list.len()
                      &&& self.free_list[pos as int] == row_addr
                  },
                  ItemRowDisposition::InPendingAllocationList{ pos, item } => {
                      &&& 0 <= pos < self.pending_allocations.len()
                      &&& self.pending_allocations[pos as int] == row_addr
                  },
                  ItemRowDisposition::InPendingDeallocationList{ pos, item } => {
                      &&& 0 <= pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[pos as int] == row_addr
                  },
                  ItemRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, item } => {
                      &&& 0 <= alloc_pos < self.pending_allocations.len()
                      &&& self.pending_allocations[alloc_pos as int] == row_addr
                      &&& 0 <= dealloc_pos < self.pending_deallocations.len()
                      &&& self.pending_deallocations[dealloc_pos as int] == row_addr
                  },
              }
        }
    }

    pub(super) open spec fn free_list_consistent(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.free_list.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.free_list[i])
            &&& self.row_info[self.free_list[i]] matches ItemRowDisposition::InFreeList{ pos }
            &&& pos == i
        }
    }

    pub(super) open spec fn pending_allocations_consistent(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.pending_allocations.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.pending_allocations[i])
            &&& match self.row_info[self.pending_allocations[i]] {
                ItemRowDisposition::InPendingAllocationList{ pos, item } => pos == i,
                ItemRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, item } => alloc_pos == i,
                _ => false,
            }
        }
    }

    pub(super) open spec fn pending_deallocations_consistent(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& forall|i: int| 0 <= i < self.pending_deallocations.len() ==> {
            &&& self.row_info.contains_key(#[trigger] self.pending_deallocations[i])
            &&& match self.row_info[self.pending_deallocations[i]] {
                ItemRowDisposition::InPendingDeallocationList{ pos, item } => pos == i,
                ItemRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, item } => dealloc_pos == i,
                _ => false,
            }
        }
    }

    pub(super) open spec fn consistent(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& self.row_info_consistent(sm)
        &&& self.free_list_consistent(sm)
        &&& self.pending_allocations_consistent(sm)
        &&& self.pending_deallocations_consistent(sm)
    }

    pub(super) open spec fn valid(self, sm: ItemTableStaticMetadata) -> bool
    {
        &&& self.complete(sm)
        &&& self.consistent(sm)
    }

    pub(super) open spec fn consistent_with_durable_state(self, s: Seq<u8>, sm: ItemTableStaticMetadata) -> bool
    {
        forall|row_addr: u64| self.row_info.contains_key(row_addr) ==>
            match self.row_info[row_addr] {
                ItemRowDisposition::NowhereFree{ item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
                ItemRowDisposition::InPendingDeallocationList{ pos, item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
                _ => true,
            }
    }

    pub(super) open spec fn consistent_with_read_state(self, s: Seq<u8>, sm: ItemTableStaticMetadata) -> bool
    {
        forall|row_addr: u64| self.row_info.contains_key(row_addr) ==>
            match self.row_info[row_addr] {
                ItemRowDisposition::NowhereFree{ item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
                ItemRowDisposition::InFreeList{ pos } => true,
                ItemRowDisposition::InPendingAllocationList{ pos, item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
                ItemRowDisposition::InPendingDeallocationList{ pos, item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
                ItemRowDisposition::InBothPendingLists{ alloc_pos, dealloc_pos, item } =>
                    recover_object::<I>(s, row_addr + sm.row_item_start, row_addr + sm.row_item_crc_start)
                        == Some(item),
            }
    }

    pub(super) open spec fn as_durable_snapshot(self) -> ItemTableSnapshot<I>
    {
        ItemTableSnapshot::<I>{
            m: Map::<u64, I>::new(
                |row_addr: u64| {
                    &&& self.row_info.contains_key(row_addr)
                    &&& self.row_info[row_addr] is NowhereFree ||
                       self.row_info[row_addr] is InPendingDeallocationList
                },
                |row_addr: u64| match self.row_info[row_addr] {
                    ItemRowDisposition::NowhereFree{ item } => item,
                    ItemRowDisposition::InPendingDeallocationList{ pos, item } => item,
                    _ => arbitrary(),
                },
            ),
        }
    }

    pub(super) open spec fn as_tentative_snapshot(self) -> ItemTableSnapshot<I>
    {
        ItemTableSnapshot::<I>{
            m: Map::<u64, I>::new(
                |row_addr: u64| {
                    &&& self.row_info.contains_key(row_addr)
                    &&& self.row_info[row_addr] is NowhereFree ||
                       self.row_info[row_addr] is InPendingAllocationList
                },
                |row_addr: u64| match self.row_info[row_addr] {
                    ItemRowDisposition::NowhereFree{ item } => item,
                    ItemRowDisposition::InPendingAllocationList{ pos, item } => item,
                    _ => arbitrary(),
                },
            ),
        }
    }

    pub(super) proof fn lemma_corresponds_implication_for_free_list_length(self, sm: ItemTableStaticMetadata)
        requires
            sm.valid::<I>(),
            self.valid(sm),
            self.pending_allocations == Seq::<u64>::empty(),
            self.pending_deallocations == Seq::<u64>::empty(),
        ensures
            self.as_durable_snapshot().m.dom().finite(),
            self.as_durable_snapshot().m.dom().len() == sm.table.num_rows - self.free_list.len(),
    {
        assert forall|pos: int| 0 <= pos < self.free_list.len() implies
            self.row_info.contains_key(#[trigger] self.free_list[pos]) by {
            assert(self.row_info[self.free_list[pos]] is InFreeList);
            assert(self.row_info.contains_key(self.free_list[pos]));
        }

        let free_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr) && self.row_info[row_addr] is InFreeList
        );
        let item_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr) && self.row_info[row_addr] is NowhereFree
        );
        let valid_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr)
        );

        assert(valid_row_addrs.finite() && valid_row_addrs.len() == sm.table.num_rows) by {
            assert(valid_row_addrs =~= Set::<u64>::new(|row_addr: u64| sm.table.validate_row_addr(row_addr)));
            sm.table.lemma_valid_row_set_len();
        }
        assert(free_row_addrs.finite()) by {
            vstd::set_lib::lemma_len_subset(free_row_addrs, valid_row_addrs);
        }
        assert(item_row_addrs.finite()) by {
            vstd::set_lib::lemma_len_subset(item_row_addrs, valid_row_addrs);
        }

        assert(valid_row_addrs.len() == free_row_addrs.len() + item_row_addrs.len()) by {
            assert(free_row_addrs.disjoint(item_row_addrs));
            assert(free_row_addrs + item_row_addrs =~= valid_row_addrs);
            vstd::set_lib::lemma_set_disjoint_lens(free_row_addrs, item_row_addrs);
        }

        assert(free_row_addrs.len() == self.free_list.len()) by {
            assert(self.free_list.to_set() =~= free_row_addrs);
            self.free_list.unique_seq_to_set();
        }

        assert(item_row_addrs =~= self.as_durable_snapshot().m.dom());
        assert(item_row_addrs.len() == sm.table.num_rows - self.free_list.len());
    }
}

impl<Perm, PermFactory, PM, I> ItemTable<Perm, PermFactory, PM, I>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    I: PmCopy + Sized + std::fmt::Debug,
{
    pub(super) open spec fn internal_view(self) -> ItemTableInternalView<I>
    {
        ItemTableInternalView::<I>{
            row_info: self.row_info@,
            free_list: self.free_list@,
            pending_allocations: self.pending_allocations@,
            pending_deallocations: self.pending_deallocations@,
        }
    }

    pub(super) open spec fn inv(self, jv: JournalView) -> bool
    {
        &&& self.sm.valid::<I>()
        &&& jv.constants.app_area_start <= self.sm.start()
        &&& self.sm.end() <= jv.constants.app_area_end
        &&& self.internal_view().valid(self.sm)
        &&& self.internal_view().consistent_with_durable_state(jv.durable_state, self.sm)
        &&& !self.must_abort@ ==> self.internal_view().consistent_with_read_state(jv.read_state, self.sm)
        &&& !self.must_abort@ ==> self.internal_view().consistent_with_read_state(jv.commit_state, self.sm)
        &&& forall|addr: int| self.sm.table.start <= addr < self.sm.table.end ==>
            !(#[trigger] jv.journaled_addrs.contains(addr))
    }

    pub proof fn lemma_valid_implications(self, jv: JournalView)
        requires
            self.valid(jv),
        ensures
            Self::recover(jv.durable_state, self@.durable.m.dom(), self@.sm) == Some(self@.durable),
            self@.tentative is Some ==>
                Self::recover(jv.commit_state, self@.tentative.unwrap().m.dom(), self@.sm) == self@.tentative,
    {
        assert(Self::recover(jv.durable_state, self@.durable.m.dom(), self@.sm) =~= Some(self@.durable));
        if self@.tentative is Some {
            assert(Self::recover(jv.commit_state, self@.tentative.unwrap().m.dom(), self@.sm) =~= self@.tentative);
        }
    }
}

}
