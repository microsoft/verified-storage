#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::kv2::items::*;
use crate::kv2::keys::*;
use crate::kv2::lists::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::kvimpl_t::*;
use super::kvshared_v::*;
use super::kvspec_t::*;

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

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KvStaticMetadata
{
    pub keys: KeyTableStaticMetadata,
    pub items: ItemTableStaticMetadata,
    pub lists: ListTableStaticMetadata,
    pub encoded_policies: u64,
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

}

