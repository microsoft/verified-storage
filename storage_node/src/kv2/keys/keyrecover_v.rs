#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::keys_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyTableRowMetadata
{
    pub item_addr: u64,
    pub list_addr: u64,
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyTableStaticMetadata
{
    pub table: TableMetadata,
    pub key_size: u64,
    pub row_cdb_start: u64,
    pub row_metadata_start: u64,
    pub row_metadata_end: u64,
    pub row_metadata_crc_start: u64,
    pub row_key_start: u64,
    pub row_key_end: u64,
    pub row_key_crc_start: u64,
}

impl KeyTableStaticMetadata
{
    pub open spec fn valid(self) -> bool
    {
        &&& self.table.valid()
        &&& self.key_size > 0
        &&& self.row_cdb_start + u64::spec_size_of() <= self.row_metadata_start
        &&& self.row_metadata_end - self.row_metadata_start == KeyTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_metadata_crc_start
        &&& self.row_metadata_crc_start + u64::spec_size_of() <= self.row_key_start
        &&& self.row_key_start + self.key_size <= self.row_key_end
        &&& self.row_key_end <= self.row_key_crc_start
        &&& self.row_key_crc_start + u64::spec_size_of() <= self.table.row_size
    }

    pub open spec fn consistent_with_type<K>(self) -> bool
        where
            K: PmCopy,
    {
        &&& self.key_size == K::spec_size_of()
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyGhostMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub row_info: Seq<Option<(K, KeyTableRowMetadata)>>,
    pub key_info: Map<K, int>,
    pub item_info: Map<u64, int>,
    pub list_info: Map<u64, int>,
}

impl<K> KeyGhostMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub open spec fn valid_row_info(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& self.row_info.len() == sm.table.num_rows
        &&& forall|row_index: int| 0 <= row_index < sm.table.num_rows ==>
            {
                let row_addr = sm.table.row_index_to_addr(row_index);
                let cdb = recover_cdb(s, row_addr + sm.row_cdb_start);
                match #[trigger] self.row_info[row_index] {
                    None => cdb == Some(false),
                    Some((k, rm)) => {
                        &&& cdb == Some(true)
                        &&& recover_object::<K>(s, row_addr + sm.row_key_start, sm.row_key_crc_start as int) == Some(k)
                        &&& recover_object::<KeyTableRowMetadata>(s, row_addr + sm.row_metadata_start,
                                                                  sm.row_metadata_crc_start as int) == Some(rm)
                        &&& self.key_info.contains_key(k)
                        &&& self.key_info[k] == row_index
                        &&& self.item_info.contains_key(rm.item_addr)
                        &&& self.item_info[rm.item_addr] == row_index
                        &&& rm.list_addr != 0 ==> self.list_info.contains_key(rm.list_addr)
                        &&& rm.list_addr != 0 ==> self.list_info[rm.list_addr] == row_index
                    },
                }
            }
    }

    pub open spec fn valid_key_info(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        forall|k: K| #[trigger] self.key_info.contains_key(k) ==>
        {
            let row_index = self.key_info[k];
            &&& 0 <= row_index < sm.table.num_rows
            &&& self.row_info[row_index] matches Some((k2, _))
            &&& k2 == k
        }
    }

    pub open spec fn valid_item_info(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        forall|item_addr: u64| #[trigger] self.item_info.contains_key(item_addr) ==>
        {
            let row_index = self.item_info[item_addr];
            &&& 0 <= row_index < sm.table.num_rows
            &&& self.row_info[row_index] matches Some((_, rm))
            &&& rm.item_addr == item_addr
        }
    }

    pub open spec fn valid_list_info(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& !self.list_info.contains_key(0)
        &&& forall|list_addr: u64| #[trigger] self.list_info.contains_key(list_addr) ==>
            {
                let row_index = self.list_info[list_addr];
                &&& 0 <= row_index < sm.table.num_rows
                &&& self.row_info[row_index] matches Some((_, rm))
                &&& rm.list_addr == list_addr
            }
    }

    pub open spec fn valid(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& self.valid_row_info(s, sm)
        &&& self.valid_key_info(s, sm)
        &&& self.valid_item_info(s, sm)
        &&& self.valid_list_info(s, sm)
    }

    pub proof fn lemma_uniqueness(self, other: Self, s: Seq<u8>, sm: KeyTableStaticMetadata)
        requires
            self.valid(s, sm),
            other.valid(s, sm),
        ensures
            self == other,
    { 
        assert(forall|row_index: int| 0 <= row_index < sm.table.num_rows ==>
               self.row_info[row_index] == other.row_info[row_index]);
        assert(self =~= other);
    }
}

pub(super) open spec fn choose_mapping<K>(s: Seq<u8>, sm: KeyTableStaticMetadata) -> KeyGhostMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    choose|mapping: KeyGhostMapping<K>| mapping.valid(s, sm)
}

pub(super) open spec fn recover_keys_from_mapping<K>(mapping: KeyGhostMapping<K>) -> KeyTableSnapshot<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    KeyTableSnapshot::<K>{
        m: Map::<K, KeyTableRowMetadata>::new(
            |k: K| mapping.key_info.contains_key(k),
            |k: K| mapping.row_info[mapping.key_info[k]].unwrap().1,
        )
    }
}

pub(super) open spec fn recover_keys<K>(
    s: Seq<u8>,
    sm: KeyTableStaticMetadata,
) -> Option<KeyTableSnapshot<K>>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    if exists|mapping: KeyGhostMapping<K>| mapping.valid(s, sm) {
        Some(recover_keys_from_mapping::<K>(choose_mapping::<K>(s, sm)))
    } else {
        None
    }
}



}
