#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::super::kvshared_v::*;
use super::super::kvspec_t::*;

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableRowMetadata
{
    pub next_row_start: u64,
    pub num_block_elements: u64,
    pub num_trimmed_elements: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct ListTableStaticMetadata
{
    pub table: TableMetadata,
    pub list_entry_size: u64,
    pub num_elements_per_block: u64,
    pub num_list_blocks: u64,
    pub row_size: u64,
    pub row_metadata_start: u64,
    pub row_metadata_end: u64,
    pub row_metadata_crc_start: u64,
    pub row_block_start: u64,
    pub row_block_end: u64,
    pub block_element_size: u64,
    pub block_element_list_entry_start: u64,
    pub block_element_list_entry_end: u64,
    pub block_element_crc_start: u64,
}

impl ListTableStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.table.valid()
        &&& self.row_metadata_end - self.row_metadata_start == ListTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_block_start
        &&& opaque_mul(self.num_elements_per_block as int, self.block_element_size as int)
            <= self.row_block_end - self.row_block_start
        &&& self.block_element_list_entry_end - self.block_element_list_entry_start == self.list_entry_size
        &&& self.block_element_list_entry_end <= self.block_element_crc_start
        &&& self.block_element_crc_start + u64::spec_size_of() <= self.block_element_size
    }

    pub open spec fn consistent_with_type<L>(self) -> bool
        where
            L: PmCopy,
    {
        &&& self.list_entry_size == L::spec_size_of()
    }
}


}
