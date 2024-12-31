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

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyEntryMetadata
{
    pub item_start: u64,
    pub list_start: u64,
}

#[verifier::ext_equal]
pub struct KvConfiguration
{
    pub journal_constants: JournalConstants,
    pub static_metadata_start: u64,
    pub static_metadata_end: u64,
    pub key_table_start: u64,
    pub key_table_end: u64,
    pub item_table_start: u64,
    pub item_table_end: u64,
    pub list_table_start: u64,
    pub list_table_end: u64,
    pub num_keys: u64,
    pub num_list_elements_per_block: u64,
    pub num_list_blocks: u64,
    pub key_size: u64,
    pub item_size: u64,
    pub list_element_size: u64,
    pub key_table_entry_size: u64,
    pub item_table_entry_size: u64,
    pub list_table_block_size: u64,
    pub list_table_entry_size: u64,
    pub key_entry_metadata_start: u64,
    pub key_entry_metadata_end: u64,
    pub key_entry_metadata_crc_start: u64,
    pub key_entry_key_start: u64,
    pub key_entry_key_end: u64,
    pub item_entry_crc_start: u64,
    pub item_entry_item_start: u64,
    pub item_entry_item_end: u64,
    pub list_entry_metadata_start: u64,
    pub list_entry_metadata_end: u64,
    pub list_entry_crc_start: u64,
    pub list_entry_element_start: u64,
    pub list_entry_element_end: u64,
}

impl KvConfiguration
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.journal_constants.valid()
        &&& self.journal_constants.app_version_number == KVSTORE_PROGRAM_VERSION_NUMBER
        &&& self.journal_constants.app_program_guid == KVSTORE_PROGRAM_GUID
        &&& self.journal_constants.app_area_start <= self.static_metadata_start
        &&& self.static_metadata_start <= self.static_metadata_end
        &&& self.static_metadata_end <= self.key_table_start
        &&& self.key_table_start <= self.key_table_end
        &&& self.key_table_end <= self.item_table_start
        &&& self.item_table_start <= self.item_table_end
        &&& self.item_table_end <= self.list_table_start
        &&& self.list_table_start <= self.list_table_end
        &&& self.list_table_end <= self.journal_constants.app_area_end
        &&& self.key_size > 0
        &&& opaque_mul(self.num_keys as int, self.key_table_entry_size as int)
            <= self.key_table_end - self.key_table_start
        &&& opaque_mul(self.num_keys as int, self.item_table_entry_size as int)
            <= self.item_table_end - self.item_table_start
        &&& opaque_mul(self.num_list_blocks as int, self.list_table_block_size as int)
            <= self.list_table_end - self.list_table_start
        &&& self.key_entry_metadata_start <= self.key_entry_metadata_end
    }
    
    pub open spec fn consistent_with_types<K, I, L>(self) -> bool
        where
            K: PmCopy,
            I: PmCopy,
            L: PmCopy,
    {
        &&& self.key_size == K::spec_size_of()
        &&& self.item_size == I::spec_size_of()
        &&& self.list_element_size == L::spec_size_of()
    }
}

}

