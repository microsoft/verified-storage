#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::super::kvimpl_t::*;
use crate::common::table_v::*;
use super::super::kvspec_t::*;

verus! {

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
pub struct KeyTableStaticMetadata
{
    pub table: TableMetadata,
    pub key_size: u64,
    pub row_metadata_start: u64,
    pub row_metadata_end: u64,
    pub row_metadata_crc_start: u64,
    pub row_key_start: u64,
    pub row_key_end: u64,
}

impl KeyTableStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.table.valid()
        &&& self.key_size > 0
        &&& self.row_metadata_end - self.row_metadata_start == KeyTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_metadata_crc_start
        &&& self.row_metadata_crc_start + u64::spec_size_of() <= self.table.row_size
    }

    pub open spec fn consistent_with_type<K>(self) -> bool
        where
            K: PmCopy,
    {
        &&& self.key_size == K::spec_size_of()
    }
}


}
