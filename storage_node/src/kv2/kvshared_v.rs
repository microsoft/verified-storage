#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::kvimpl_t::*;
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
    pub key_table_start: u64,
    pub key_table_end: u64,
    pub item_table_start: u64,
    pub item_table_end: u64,
    pub list_table_start: u64,
    pub list_table_end: u64,
    pub encoded_policies: u64,
    pub num_keys: u64,
    pub num_list_entries_per_block: u64,
    pub num_list_blocks: u64,
    pub key_size: u64,
    pub item_size: u64,
    pub list_entry_size: u64,
    pub key_table_row_size: u64,
    pub item_table_row_size: u64,
    pub list_table_row_size: u64,
    pub list_block_element_size: u64,
    pub key_table_row_metadata_start: u64,
    pub key_table_row_metadata_end: u64,
    pub key_table_row_metadata_crc_start: u64,
    pub key_table_row_key_start: u64,
    pub key_table_row_key_end: u64,
    pub item_table_row_item_start: u64,
    pub item_table_row_item_end: u64,
    pub item_table_row_item_crc_start: u64,
    pub list_table_row_metadata_start: u64,
    pub list_table_row_metadata_end: u64,
    pub list_table_row_metadata_crc_start: u64,
    pub list_table_row_block_start: u64,
    pub list_table_row_block_end: u64,
    pub list_block_element_list_entry_start: u64,
    pub list_block_element_list_entry_end: u64,
    pub list_block_element_crc_start: u64,
}

impl KvStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.key_table_start <= self.key_table_end
        &&& self.key_table_end <= self.item_table_start
        &&& self.item_table_start <= self.item_table_end
        &&& self.item_table_end <= self.list_table_start
        &&& self.list_table_start <= self.list_table_end
        &&& self.key_size > 0
        &&& opaque_mul(self.num_keys as int, self.key_table_row_size as int) <= self.key_table_end - self.key_table_start
        &&& self.key_table_row_metadata_end - self.key_table_row_metadata_start == KeyTableRowMetadata::spec_size_of()
        &&& self.key_table_row_metadata_end <= self.key_table_row_metadata_crc_start
        &&& self.key_table_row_metadata_crc_start + u64::spec_size_of() <= self.key_table_row_size
        &&& opaque_mul(self.num_keys as int, self.item_table_row_size as int) <= self.item_table_end - self.item_table_start
        &&& self.item_table_row_item_end - self.item_table_row_item_start == self.item_size
        &&& self.item_table_row_item_end <= self.item_table_row_item_crc_start
        &&& self.item_table_row_item_crc_start + u64::spec_size_of() <= self.item_table_row_size
        &&& opaque_mul(self.num_list_blocks as int, self.list_table_row_size as int)
            <= self.list_table_end - self.list_table_start
        &&& self.list_table_row_metadata_end - self.list_table_row_metadata_start == ListTableRowMetadata::spec_size_of()
        &&& self.list_table_row_metadata_end <= self.list_table_row_block_start
        &&& opaque_mul(self.num_list_entries_per_block as int, self.list_block_element_size as int)
            <= self.list_table_row_block_end - self.list_table_row_block_start
        &&& self.list_block_element_list_entry_end - self.list_block_element_list_entry_start == self.list_entry_size
        &&& self.list_block_element_list_entry_end <= self.list_block_element_crc_start
        &&& self.list_block_element_crc_start + u64::spec_size_of() <= self.list_block_element_size
    }

    pub open spec fn consistent_with_types<K, I, L>(self) -> bool
        where
            K: PmCopy,
            I: PmCopy,
            L: PmCopy,
    {
        &&& self.key_size == K::spec_size_of()
        &&& self.item_size == I::spec_size_of()
        &&& self.list_entry_size == L::spec_size_of()
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

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyTableRowMetadata
{
    pub item_start: u64,
    pub list_start: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableRowMetadata
{
    pub next_row_start: u64,
    pub num_block_elements: u64,
    pub num_trimmed_elements: u64,
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
        &&& self.static_metadata_end <= self.sm.key_table_start
        &&& self.sm.list_table_end <= self.journal_constants.app_area_end
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

