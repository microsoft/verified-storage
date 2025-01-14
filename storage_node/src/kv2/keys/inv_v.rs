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

verus! {

#[verifier::ext_equal]
pub(super) enum KeyTableStatus {
    Quiescent,
}

#[verifier::ext_equal]
pub(super) struct ConcreteKeyInfo
{
    pub row_addr: u64,
    pub rm: KeyTableRowMetadata,
}

#[verifier::ext_equal]
pub(super) enum KeyUndoRecord<K> {
    UndoCreate{ row_addr: u64 },
    UndoUpdate{ row_addr: u64, former_rm: KeyTableRowMetadata },
    UndoDelete{ row_addr: u64, k: K, rm: KeyTableRowMetadata },
}

#[verifier::ext_equal]
pub(super) enum KeyRowDisposition<K> {
    InHashTable{ k: K, rm: KeyTableRowMetadata },
    InFreeList{ pos: nat },
    InPendingDeallocationList{ pos: nat },
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub(super) struct KeyMemoryMapping<K> {
    pub sm: KeyTableStaticMetadata,
    pub row_info: Map<u64, KeyRowDisposition<K>>,
    pub key_info: Map<K, u64>,
    pub item_info: Map<u64, u64>,
    pub list_info: Map<u64, u64>,
}

impl<K> KeyMemoryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub open spec fn as_recovery_mapping(self) -> KeyRecoveryMapping<K>
    {
        KeyRecoveryMapping::<K>{
            row_info: Map::<u64, Option<(K, KeyTableRowMetadata)>>::new(
                |row_addr: u64| self.row_info.contains_key(row_addr),
                |row_addr: u64| match self.row_info[row_addr] {
                    KeyRowDisposition::InHashTable{ k, rm } => Some((k, rm)),
                    _ => None,
                },
            ),
            key_info: Map::<K, u64>::new(
                |k: K| self.key_info.contains_key(k),
                |k: K| self.key_info[k] as u64,
            ),
            item_info: Map::<u64, u64>::new(
                |item_addr: u64| self.item_info.contains_key(item_addr),
                |item_addr: u64| self.item_info[item_addr] as u64,
            ),
            list_info: Map::<u64, u64>::new(
                |list_addr: u64| self.list_info.contains_key(list_addr),
                |list_addr: u64| self.list_info[list_addr] as u64,
            ),
        }
    }

    pub(super) open spec fn as_snapshot(self) -> KeyTableSnapshot<K>
    {
        KeyTableSnapshot::<K>{
            key_info: Map::<K, KeyTableRowMetadata>::new(
                |k: K| self.key_info.contains_key(k),
                |k: K| self.row_info[self.key_info[k]]->rm,
            ),
            item_info: Map::<u64, K>::new(
                |item_addr: u64| self.item_info.contains_key(item_addr),
                |item_addr: u64| self.row_info[self.item_info[item_addr]]->k
            ),
            list_info: Map::<u64, K>::new(
                |list_addr: u64| self.list_info.contains_key(list_addr),
                |list_addr: u64| self.row_info[self.list_info[list_addr]]->k
            ),
        }
    }

    pub(super) open spec fn row_info_valid(self) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.sm.table.validate_row_addr(row_addr) <==>
                self.row_info.contains_key(row_addr)
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            &&& self.sm.table.validate_row_addr(row_addr)
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k, rm } ==> {
                    &&& self.key_info.contains_key(k)
                    &&& self.key_info[k] == row_addr
                    &&& self.item_info.contains_key(rm.item_addr)
                    &&& self.item_info[rm.item_addr] == row_addr
                    &&& rm.list_addr != 0 ==> self.list_info.contains_key(rm.list_addr)
                    &&& rm.list_addr != 0 ==> self.list_info[rm.list_addr] == row_addr
                }
        }
    }

    pub(super) open spec fn key_info_valid(self) -> bool
    {
        &&& forall|k: K| #[trigger] self.key_info.contains_key(k) ==> {
            let row_addr = self.key_info[k];
            &&& self.row_info.contains_key(row_addr)
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: k2, rm: _ }
            &&& k == k2
        }
    }

    pub(super) open spec fn item_info_valid(self) -> bool
    {
        &&& forall|item_addr: u64| #[trigger] self.item_info.contains_key(item_addr) ==> {
            let row_addr = self.item_info[item_addr];
            &&& self.row_info.contains_key(row_addr)
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: _, rm }
            &&& rm.item_addr == item_addr
        }
    }

    pub(super) open spec fn list_info_valid(self) -> bool
    {
        &&& forall|list_addr: u64| #[trigger] self.list_info.contains_key(list_addr) ==> {
            let row_addr = self.list_info[list_addr];
            &&& self.row_info.contains_key(row_addr)
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: _, rm }
            &&& rm.list_addr == list_addr
        }
    }

    pub(super) open spec fn valid(self) -> bool
    {
        &&& self.row_info_valid()
        &&& self.key_info_valid()
        &&& self.item_info_valid()
        &&& self.list_info_valid()
    }

    pub(super) open spec fn consistent_with_state(self, s: Seq<u8>) -> bool
    {
        forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            let cdb = recover_cdb(s, row_addr + self.sm.row_cdb_start);
            match self.row_info[row_addr] {
                KeyRowDisposition::InHashTable{ k, rm } => {
                    &&& cdb == Some(true)
                    &&& recover_object::<K>(s, row_addr + self.sm.row_key_start,
                                            row_addr + self.sm.row_key_crc_start as u64) == Some(k)
                    &&& recover_object::<KeyTableRowMetadata>(s, row_addr + self.sm.row_metadata_start,
                                                                row_addr + self.sm.row_metadata_crc_start) == Some(rm)
                },
                _ => cdb == Some(false),
            }
        }
    }

    pub(super) open spec fn consistent_with_free_list_and_pending_deallocations(self, free_list: Seq<u64>, pending_deallocations: Seq<u64>) -> bool
    {
        &&& forall|row_addr: u64| #[trigger] self.row_info.contains_key(row_addr) ==> {
            match self.row_info[row_addr] {
                KeyRowDisposition::InFreeList{ pos } => {
                    &&& pos < free_list.len()
                    &&& free_list[pos as int] == row_addr
                },
                KeyRowDisposition::InPendingDeallocationList{ pos } => {
                    &&& pos < pending_deallocations.len()
                    &&& pending_deallocations[pos as int] == row_addr
                },
                _ => true,
            }
        }
        &&& forall|i: int| 0 <= i < free_list.len() ==> {
            &&& #[trigger] self.row_info[free_list[i]] matches KeyRowDisposition::InFreeList{ pos }
            &&& pos == i
        }
        &&& forall|i: int| 0 <= i < pending_deallocations.len() ==> {
            &&& #[trigger] self.row_info[pending_deallocations[i]] matches KeyRowDisposition::InPendingDeallocationList{ pos }
            &&& pos == i
        }
    }

    pub(super) open spec fn undo_create(self, row_addr: u64, k: K, rm: KeyTableRowMetadata, free_list_pos: nat)
                                        -> Option<Self>
    {
        if {
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: k2, rm: rm2 }
            &&& k == k2
            &&& rm == rm2
        } {
            Some(Self{
                row_info: self.row_info.insert(row_addr, KeyRowDisposition::InFreeList{ pos: free_list_pos }),
                key_info: self.key_info.remove(k),
                item_info: self.item_info.remove(rm.item_addr),
                list_info: self.list_info.remove(rm.list_addr),
                ..self
            })
        }
        else {
            None
        }
    }

    pub(super) open spec fn undo_update(self, row_addr: u64, k: K, former_rm: KeyTableRowMetadata) -> Option<Self>
    {
        if {
            &&& self.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: k2, rm: _ }
            &&& k == k2
        } {
            Some(Self{
                row_info: self.row_info.insert(row_addr, KeyRowDisposition::InHashTable{ k, rm: former_rm }),
                ..self
            })
        }
        else {
            None
        }
    }

    pub(super) open spec fn undo_delete(self, row_addr: u64, k: K, rm: KeyTableRowMetadata) -> Option<Self>
    {
        if {
            &&& self.row_info[row_addr] matches KeyRowDisposition::InPendingDeallocationList{ pos }
        } {
            Some(Self{
                row_info: self.row_info.insert(row_addr, KeyRowDisposition::InHashTable{ k, rm }),
                key_info: self.key_info.insert(k, row_addr),
                item_info: self.item_info.insert(rm.item_addr, row_addr),
                list_info: self.list_info.insert(rm.list_addr, row_addr),
                ..self
            })
        } else {
            None
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub(super) struct KeyInternalView<K> {
    pub sm: KeyTableStaticMetadata,
    pub m: Map<K, ConcreteKeyInfo>,
    pub free_list: Seq<u64>,
    pub pending_deallocations: Seq<u64>,
    pub memory_mapping: KeyMemoryMapping<K>,
}

impl<K> KeyInternalView<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub(super) open spec fn valid(self) -> bool
    {
        &&& forall|k: K| #[trigger] self.memory_mapping.key_info.contains_key(k) ==> {
            let row_addr = self.memory_mapping.key_info[k];
            &&& self.m.contains_key(k)
            &&& self.m[k].row_addr == row_addr
            &&& self.memory_mapping.row_info[row_addr] matches KeyRowDisposition::InHashTable{ k: k2, rm }
            &&& k2 == k
            &&& rm == self.m[k].rm
        }
        &&& forall|k: K| #[trigger] self.m.contains_key(k) ==> self.memory_mapping.key_info.contains_key(k)
    }

    pub(super) open spec fn consistent_with_journaled_addrs(self, journaled_addrs: Set<int>) -> bool
    {
        &&& forall|row_addr: u64, addr: int| {
            &&& #[trigger] self.free_list.contains(row_addr)
            &&& row_addr <= addr < row_addr + self.sm.table.row_size
        } ==> !(#[trigger] journaled_addrs.contains(addr))
    }

    pub(super) open spec fn apply_undo_record(self, record: KeyUndoRecord<K>) -> Option<Self>
    {
        match record {
            KeyUndoRecord::UndoCreate{ row_addr } =>
            {
                match self.memory_mapping.row_info[row_addr] {
                    KeyRowDisposition::InHashTable{ k, rm } => {
                        match self.memory_mapping.undo_create(row_addr, k, rm, self.free_list.len()) {
                            Some(memory_mapping) => Some(Self{
                                m: self.m.remove(k),
                                free_list: self.free_list.push(row_addr),
                                memory_mapping,
                                ..self
                            }),
                            None => None,
                        }
                    },
                    _ => None,
                }
            },
            KeyUndoRecord::UndoUpdate{ row_addr, former_rm } =>
            {
                match self.memory_mapping.row_info[row_addr] {
                    KeyRowDisposition::InHashTable{ k, rm } => {
                        match self.memory_mapping.undo_update(row_addr, k, former_rm) {
                            Some(memory_mapping) => Some(Self{
                                m: self.m.insert(k, ConcreteKeyInfo{ row_addr, rm: former_rm }),
                                memory_mapping,
                                ..self
                            }),
                            None => None,
                        }
                    },
                    _ => None,
                }
            },
            KeyUndoRecord::UndoDelete{ row_addr, k, rm } =>
            {
                match self.memory_mapping.row_info[row_addr] {
                    KeyRowDisposition::InPendingDeallocationList{ pos } => {
                        if pos + 1 != self.pending_deallocations.len() {
                            None
                        }
                        else {
                            match self.memory_mapping.undo_delete(row_addr, k, rm) {
                                Some(memory_mapping) => Some(Self{
                                    m: self.m.remove(k),
                                    pending_deallocations: self.pending_deallocations.drop_last(),
                                    memory_mapping,
                                    ..self
                                }),
                                None => None,
                            }
                        }
                    },
                    _ => None,
                }
            },
        }
    }

    pub(super) open spec fn apply_undo_record_list(self, records: Seq<KeyUndoRecord<K>>) -> Option<Self>
        decreases
            records.len()
    {
        if records.len() == 0 {
            Some(self)
        }
        else {
            match self.apply_undo_record(records.last()) {
                Some(new_self) => new_self.apply_undo_record_list(records.drop_last()),
                None => None,
            }
        }
    }

    pub(super) open spec fn consistent_with_state(self, s: Seq<u8>) -> bool
    {
        &&& self.memory_mapping.valid()
        &&& self.memory_mapping.consistent_with_state(s)
        &&& self.memory_mapping.consistent_with_free_list_and_pending_deallocations(self.free_list, self.pending_deallocations)
    }


    pub(super) open spec fn consistent_with_journal(self, undo_records: Seq<KeyUndoRecord<K>>, jv: JournalView) -> bool
    {
        &&& self.valid()
        &&& self.consistent_with_state(jv.commit_state)
        &&& self.consistent_with_journaled_addrs(jv.journaled_addrs)
        &&& self.apply_undo_record_list(undo_records) matches Some(undone_self)
        &&& undone_self.valid()
        &&& undone_self.consistent_with_state(jv.durable_state)
    }

    pub(super) open spec fn as_snapshot(self) -> KeyTableSnapshot<K>
    {
        self.memory_mapping.as_snapshot()
    }
}

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub(super) open spec fn internal_view(self) -> KeyInternalView<K>
    {
        KeyInternalView::<K>{
            sm: self.sm,
            m: self.m@,
            free_list: self.free_list@,
            pending_deallocations: self.pending_deallocations@,
            memory_mapping: self.memory_mapping@,
        }
    }

    pub(super) open spec fn inv(self, jv: JournalView) -> bool
    {
        &&& vstd::std_specs::hash::obeys_key_model::<K>()
        &&& self.internal_view().consistent_with_journal(self.undo_records@, jv)
    }

    pub proof fn lemma_valid_implications(&self, jv: JournalView)
        requires
            self.valid(jv),
        ensures
            self@.durable.valid(),
            self@.tentative matches Some(tentative) ==> tentative.valid(),
            Self::recover(jv.durable_state, self@.sm) == Some(self@.durable),
            self@.tentative is Some ==> Self::recover(jv.commit_state, self@.sm) == self@.tentative,
    {
        assume(false);
    }

}

}

