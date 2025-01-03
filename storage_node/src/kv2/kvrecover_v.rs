#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::keys::*;
use super::items::*;
use super::kvimpl_t::*;
use super::kvspec_t::*;
use super::lists::*;

verus! {

// This GUID was generated randomly and is meant to describe the
// journal module, even if it has future versions.

pub const KVSTORE_PROGRAM_GUID: u128 = 0x256e549674024fd4880381d8010e6f54;

// The current version number, and the only one whose contents
// this program can read, is the following:

pub const KVSTORE_PROGRAM_VERSION_NUMBER: u64 = 1;

pub open spec fn encode_policies(logical_range_gaps_policy: LogicalRangeGapsPolicy) -> u64
{
    match logical_range_gaps_policy {
        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden => 0,
        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted => 1,
    }
}

pub open spec fn decode_policies(encoded_policy: u64) -> Option<LogicalRangeGapsPolicy>
{
    if encoded_policy == 0 {
        Some(LogicalRangeGapsPolicy::LogicalRangeGapsForbidden)
    }
    else if encoded_policy == 1 {
        Some(LogicalRangeGapsPolicy::LogicalRangeGapsPermitted)
    }
    else {
        None
    }
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KvStaticMetadata
{
    pub encoded_policies: u64,
    pub keys: KeyTableStaticMetadata,
    pub items: ItemTableStaticMetadata,
    pub lists: ListTableStaticMetadata,
    pub id: u128,
}

impl KvStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.keys.valid()
        &&& self.items.valid()
        &&& self.lists.valid()
        &&& self.keys.table.num_rows == self.items.table.num_rows
        &&& self.keys.table.end <= self.items.table.start
        &&& self.items.table.end <= self.lists.table.start
    }

    pub open spec fn consistent_with_types<K, I, L>(self) -> bool
        where
            K: PmCopy,
            I: PmCopy,
            L: PmCopy,
    {
        &&& self.keys.consistent_with_type::<K>()
        &&& self.items.consistent_with_type::<I>()
        &&& self.lists.consistent_with_type::<L>()
    }
}

#[verifier::ext_equal]
pub struct KvConfiguration
{
    pub journal_constants: JournalConstants,
    pub logical_range_gaps_policy: LogicalRangeGapsPolicy,
    pub static_metadata_start: u64,
    pub static_metadata_end: u64,
    pub sm: KvStaticMetadata,
}

impl KvConfiguration
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.journal_constants.valid()
        &&& self.journal_constants.app_version_number == KVSTORE_PROGRAM_VERSION_NUMBER
        &&& self.journal_constants.app_program_guid == KVSTORE_PROGRAM_GUID
        &&& self.journal_constants.app_area_start <= self.static_metadata_start
        &&& self.static_metadata_end - self.static_metadata_start == KvStaticMetadata::spec_size_of()
        &&& self.static_metadata_end <= self.sm.keys.table.start
        &&& self.sm.lists.table.end <= self.journal_constants.app_area_end
        &&& self.sm.valid()
        &&& self.sm.encoded_policies == encode_policies(self.logical_range_gaps_policy)
    }

    pub open spec fn consistent_with_types<K, I, L>(self) -> bool
        where
            K: PmCopy,
            I: PmCopy,
            L: PmCopy,
    {
        self.sm.consistent_with_types::<K, I, L>()
    }
}

pub(super) open spec fn validate_static_metadata(sm: KvStaticMetadata, jc: JournalConstants) -> bool
{
    &&& sm.valid()
    &&& jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() <= sm.keys.table.start
    &&& sm.lists.table.end <= jc.app_area_end
}

pub(super) open spec fn recover_static_metadata(bytes: Seq<u8>, jc: JournalConstants) -> Option<KvStaticMetadata>
{
    if jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() > jc.app_area_end {
        None
    }
    else {
        match recover_object::<KvStaticMetadata>(bytes, jc.app_area_start as int,
                                                 jc.app_area_start + KvStaticMetadata::spec_size_of()) {
            None => None,
            Some(sm) => if validate_static_metadata(sm, jc) { Some(sm) } else { None },
        }
    }
}

pub(super) open spec fn recover_kv_from_keys_items_and_lists<PM, K, I, L>(
    id: u128,
    logical_range_gaps_policy: LogicalRangeGapsPolicy,
    keys: Map<K, KeyTableRowMetadata>,
    items: Map<u64, I>,
    lists: Map<u64, Seq<L>>,
) -> Option<AtomicKvStore<K, I, L>>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    Some(
        AtomicKvStore::<K, I, L>{
            id,
            logical_range_gaps_policy,
            m: Map::<K, (I, Seq<L>)>::new(
                |k: K| keys.dom().contains(k),
                |k: K| (items[keys[k].item_start], lists[keys[k].list_start]),
            )
        }
    )
}

pub(super) open spec fn recover_kv_from_static_metadata<PM, K, I, L>(bytes: Seq<u8>, sm: KvStaticMetadata)
                                                                     -> Option<AtomicKvStore<K, I, L>>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    match KeyTable::<PM, K>::recover(bytes, sm.keys) {
        None => None,
        Some(keys) => {
            match ItemTable::<PM, I>::recover(bytes, keys.item_addrs(), sm.items) {
                None => None,
                Some(items) => {
                    match ListTable::<PM, L>::recover(bytes, keys.list_addrs(), sm.lists) {
                        None => None,
                        Some(lists) => {
                            match decode_policies(sm.encoded_policies) {
                                None => None,
                                Some(policy) => recover_kv_from_keys_items_and_lists::<PM, K, I, L>(
                                    sm.id, policy, keys.m, items.m, lists.m
                                ),
                            }
                        },
                    }
                },
            }
        },
    }
}

pub(super) open spec fn recover_kv<PM, K, I, L>(bytes: Seq<u8>, jc: JournalConstants) -> Option<AtomicKvStore<K, I, L>>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    if jc.app_program_guid != KVSTORE_PROGRAM_GUID {
        None
    }
    else if jc.app_version_number != KVSTORE_PROGRAM_VERSION_NUMBER {
        None
    }
    else {
        match recover_static_metadata(bytes, jc) {
            None => None,
            Some(sm) => recover_kv_from_static_metadata::<PM, K, I, L>(bytes, sm),
        }
    }
}

}

