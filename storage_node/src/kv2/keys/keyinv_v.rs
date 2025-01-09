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
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::ext_equal]
pub(super) enum KeyTableStatus {
    Quiescent,
}

#[verifier::ext_equal]
pub(super) struct ConcreteKeyInfo
{
    row_addr: u64,
    rm: KeyTableRowMetadata,
}

#[verifier::ext_equal]
pub(super) enum KeyRowDisposition<K> {
    Valid{ k: K, rm: KeyTableRowMetadata },
    InFreeList{ pos: nat },
    InPendingAllocationList{ pos: nat },
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub(super) struct KeyMemoryMapping<K> {
    pub row_info: Map<int, KeyRowDisposition<K>>,
    pub key_info: Map<K, int>,
    pub item_info: Map<u64, int>,
    pub list_info: Map<u64, int>,
}

impl<K> KeyMemoryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub open spec fn as_recovery_mapping(self) -> KeyRecoveryMapping<K>
    {
        KeyRecoveryMapping::<K>{
            row_info: Map::<int, Option<(K, KeyTableRowMetadata)>>::new(
                |row_addr: int| self.row_info.contains_key(row_addr),
                |row_addr: int| match self.row_info[row_addr] {
                    KeyRowDisposition::Valid{ k, rm } => Some((k, rm)),
                    _ => None,
                },
            ),
            key_info: Map::<K, int>::new(
                |k: K| self.key_info.contains_key(k),
                |k: K| self.key_info[k] as int,
            ),
            item_info: Map::<u64, int>::new(
                |item_addr: u64| self.item_info.contains_key(item_addr),
                |item_addr: u64| self.item_info[item_addr] as int,
            ),
            list_info: Map::<u64, int>::new(
                |list_addr: u64| self.list_info.contains_key(list_addr),
                |list_addr: u64| self.list_info[list_addr] as int,
            ),
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub(super) struct KeyInternalView<K> {
    pub m: Map<K, ConcreteKeyInfo>,
    pub free_list: Seq<u64>,
    pub pending_deallocations: Seq<u64>,
    pub memory_mapping: KeyMemoryMapping<K>,
}

impl<K> KeyInternalView<K>
{
    pub(super) open spec fn keys_consistent_with(self, sm: KeyTableStaticMetadata, jv: JournalView) -> bool
    {
        true
    }

    pub(super) open spec fn consistent_with(self, sm: KeyTableStaticMetadata, jv: JournalView) -> bool
    {
        &&& self.keys_consistent_with(sm, jv)
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
            m: self.m@,
            free_list: self.free_list@,
            pending_deallocations: self.pending_deallocations@,
            memory_mapping: self.memory_mapping@,
        }
    }

    pub(super) open spec fn inv(self, sm: KeyTableStaticMetadata, jv: JournalView) -> bool
    {
        &&& self.internal_view().consistent_with(sm, jv)
    }
}

}

