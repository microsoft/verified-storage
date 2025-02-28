#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
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
use super::impl_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::spec_t::*;

verus! {

// This GUID was generated randomly and is meant to describe the
// journal module, even if it has future versions.

pub const KVSTORE_PROGRAM_GUID: u128 = 0x256e549674024fd4880381d8010e6f54;

// The current version number, and the only one whose contents
// this program can read, is the following:

pub const KVSTORE_PROGRAM_VERSION_NUMBER: u64 = 1;

pub open spec fn spec_encode_policies(logical_range_gaps_policy: LogicalRangeGapsPolicy) -> u64
{
    match logical_range_gaps_policy {
        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden => 0,
        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted => 1,
    }
}

pub open spec fn spec_decode_policies(encoded_policy: u64) -> Option<LogicalRangeGapsPolicy>
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

pub exec fn encode_policies(logical_range_gaps_policy: &LogicalRangeGapsPolicy) -> (result: u64)
    ensures
        result == spec_encode_policies(*logical_range_gaps_policy),
{
    match logical_range_gaps_policy {
        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden => 0,
        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted => 1,
    }
}

#[verifier::when_used_as_spec(spec_decode_policies)]
pub exec fn decode_policies(encoded_policy: u64) -> (result: Option<LogicalRangeGapsPolicy>)
    ensures
        result == spec_decode_policies(encoded_policy),
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
    pub id: u128,
    pub encoded_policies: u64,
    pub max_keys: u64,
    pub max_list_entries: u64,
    pub max_operations_per_transaction: u64,
    pub keys: KeyTableStaticMetadata,
    pub items: ItemTableStaticMetadata,
    pub lists: ListTableStaticMetadata,
}

impl KvStaticMetadata
{
    pub open spec fn valid<K, I, L>(self) -> bool
        where
            K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
            I: PmCopy + std::fmt::Debug,
            L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    {
        &&& self.keys.valid::<K>()
        &&& self.items.valid::<I>()
        &&& self.lists.valid::<L>()
        &&& self.keys.num_rows() == self.items.num_rows()
        &&& self.keys.end() <= self.items.start()
        &&& self.items.end() <= self.lists.start()
        &&& self.keys.num_rows() >= self.max_keys
        &&& self.items.num_rows() >= self.max_keys
        &&& self.lists.num_rows() >= self.max_list_entries
        &&& decode_policies(self.encoded_policies) is Some
    }
}

pub(super) open spec fn validate_static_metadata<K, I, L>(sm: KvStaticMetadata, jc: JournalConstants) -> bool
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    &&& sm.valid::<K, I, L>()
    &&& jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() <= sm.keys.start()
    &&& sm.keys.start() <= sm.keys.end()
    &&& sm.keys.end() <= sm.items.start()
    &&& sm.items.start() <= sm.items.end()
    &&& sm.items.end() <= sm.lists.start()
    &&& sm.lists.start() <= sm.lists.end()
    &&& sm.lists.end() <= jc.app_area_end
}

#[verifier::opaque]
pub(super) open spec fn recover_static_metadata<K, I, L>(bytes: Seq<u8>, jc: JournalConstants)
                                                         -> Option<KvStaticMetadata>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    if jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() > jc.app_area_end {
        None
    }
    else {
        match recover_object::<KvStaticMetadata>(bytes, jc.app_area_start as int,
                                                 jc.app_area_start + KvStaticMetadata::spec_size_of()) {
            None => None,
            Some(sm) => if validate_static_metadata::<K, I, L>(sm, jc) { Some(sm) } else { None },
        }
    }
}

pub(super) open spec fn recover_kv_from_keys_items_and_lists<PM, K, I, L>(
    id: u128,
    logical_range_gaps_policy: LogicalRangeGapsPolicy,
    max_keys: u64,
    max_list_entries: u64,
    max_operations_per_transaction: u64,
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
                |k: K| (items[keys[k].item_addr],
                        if keys[k].list_addr == 0 { Seq::<L>::empty() } else { lists[keys[k].list_addr] }),
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
                                    sm.id, policy, sm.max_keys, sm.max_list_entries,
                                    sm.max_operations_per_transaction, keys.key_info, items.m, lists.m
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
        match recover_static_metadata::<K, I, L>(bytes, jc) {
            None => None,
            Some(sm) => recover_kv_from_static_metadata::<PM, K, I, L>(bytes, sm),
        }
    }
}

pub(super) open spec fn recover_journal_then_kv<PM, K, I, L>(bytes: Seq<u8>) -> Option<AtomicKvStore<K, I, L>>
    where
        PM: PersistentMemoryRegion,
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    match Journal::<TrustedKvPermission, PM>::recover(bytes) {
        None => None,
        Some(RecoveredJournal{ constants, state }) => recover_kv::<PM, K, I, L>(state, constants),
    }
}

pub(super) open spec fn states_match_in_static_metadata_area(s1: Seq<u8>, s2: Seq<u8>, jc: JournalConstants) -> bool
{
    seqs_match_in_range(s1, s2, jc.app_area_start as int,
                        jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of())
}

pub(super) proof fn lemma_recover_static_metadata_depends_only_on_its_area<K, I, L>(
    s1: Seq<u8>,
    s2: Seq<u8>,
    sm: KvStaticMetadata,
    jc: JournalConstants,
)
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
    requires
        validate_static_metadata::<K, I, L>(sm, jc),
        states_match_in_static_metadata_area(s1, s2, jc),
        recover_static_metadata::<K, I, L>(s1, jc) == Some(sm),
    ensures
        recover_static_metadata::<K, I, L>(s2, jc) == Some(sm),
{
    broadcast use broadcast_seqs_match_in_range_can_narrow_range;
    reveal(recover_static_metadata);
    assert(recover_static_metadata::<K, I, L>(s2, jc) =~= Some(sm));
}

pub(super) open spec fn combine_component_snapshots<K, I, L>(
    id: u128,
    logical_range_gaps_policy: LogicalRangeGapsPolicy,
    keys: KeyTableSnapshot<K>,
    items: ItemTableSnapshot<I>,
    lists: ListTableSnapshot<L>,
) -> AtomicKvStore<K, I, L>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    AtomicKvStore::<K, I, L>{
        id,
        logical_range_gaps_policy,
        m: Map::<K, (I, Seq<L>)>::new(
            |k: K| keys.key_info.dom().contains(k),
            |k: K| (items.m[keys.key_info[k].item_addr],
                    if keys.key_info[k].list_addr == 0 { Seq::<L>::empty() }
                    else { lists.m[keys.key_info[k].list_addr] }),
        )
    }
}

}

