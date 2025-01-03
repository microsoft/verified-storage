#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::recover_v::*;
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
pub struct KeyRecoveryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub row_info: Map<int, Option<(K, KeyTableRowMetadata)>>,
    pub key_info: Map<K, int>,
    pub item_info: Map<u64, int>,
    pub list_info: Map<u64, int>,
}

impl<K> KeyRecoveryMapping<K>
    where
        K: Hash + Eq + Clone + PmCopy + std::fmt::Debug,
{
    pub(super) open spec fn new(s: Seq<u8>, sm: KeyTableStaticMetadata) -> Option<Self>
    {
        if exists|mapping: Self| mapping.corresponds(s, sm) {
            Some(choose|mapping: KeyRecoveryMapping<K>| mapping.corresponds(s, sm))
        }
        else {
            None
        }
    }
    
    pub(super) open spec fn row_info_corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& forall|row_addr: int| #[trigger] sm.table.validate_row_addr(row_addr) ==>
                self.row_info.contains_key(row_addr)
        &&& forall|row_addr: int| #[trigger] self.row_info.contains_key(row_addr) ==>
            {
                let cdb = recover_cdb(s, row_addr + sm.row_cdb_start);
                &&& sm.table.validate_row_addr(row_addr)
                &&& match self.row_info[row_addr] {
                    None => cdb == Some(false),
                    Some((k, rm)) => {
                        &&& cdb == Some(true)
                        &&& recover_object::<K>(s, row_addr + sm.row_key_start, sm.row_key_crc_start as int) == Some(k)
                        &&& recover_object::<KeyTableRowMetadata>(s, row_addr + sm.row_metadata_start,
                                                                 sm.row_metadata_crc_start as int) == Some(rm)
                        &&& self.key_info.contains_key(k)
                        &&& self.key_info[k] == row_addr
                        &&& self.item_info.contains_key(rm.item_addr)
                        &&& self.item_info[rm.item_addr] == row_addr
                        &&& rm.list_addr != 0 ==> self.list_info.contains_key(rm.list_addr)
                        &&& rm.list_addr != 0 ==> self.list_info[rm.list_addr] == row_addr
                    },
                }
            }
    }

    pub(super) open spec fn key_info_corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        forall|k: K| #[trigger] self.key_info.contains_key(k) ==>
        {
            let row_addr = self.key_info[k];
            &&& sm.table.validate_row_addr(row_addr)
            &&& self.row_info[row_addr] matches Some((k2, _))
            &&& k2 == k
        }
    }

    pub(super) open spec fn item_info_corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        forall|item_addr: u64| #[trigger] self.item_info.contains_key(item_addr) ==>
        {
            let row_addr = self.item_info[item_addr];
            &&& sm.table.validate_row_addr(row_addr)
            &&& self.row_info[row_addr] matches Some((_, rm))
            &&& rm.item_addr == item_addr
        }
    }

    pub(super) open spec fn list_info_corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& !self.list_info.contains_key(0)
        &&& forall|list_addr: u64| #[trigger] self.list_info.contains_key(list_addr) ==>
            {
                let row_addr = self.list_info[list_addr];
                &&& sm.table.validate_row_addr(row_addr)
                &&& self.row_info[row_addr] matches Some((_, rm))
                &&& rm.list_addr == list_addr
            }
    }

    pub(super) open spec fn corresponds(self, s: Seq<u8>, sm: KeyTableStaticMetadata) -> bool
    {
        &&& self.row_info_corresponds(s, sm)
        &&& self.key_info_corresponds(s, sm)
        &&& self.item_info_corresponds(s, sm)
        &&& self.list_info_corresponds(s, sm)
    }

    pub(super) proof fn lemma_uniqueness(self, other: Self, s: Seq<u8>, sm: KeyTableStaticMetadata)
        requires
            self.corresponds(s, sm),
            other.corresponds(s, sm),
        ensures
            self == other,
    { 
        assert(self =~= other);
    }

    pub(super) proof fn lemma_corresponds_implies_equals_new(self, s: Seq<u8>, sm: KeyTableStaticMetadata)
        requires
            self.corresponds(s, sm),
        ensures
            Self::new(s, sm) == Some(self),
    {
        self.lemma_uniqueness(Self::new(s, sm).unwrap(), s, sm);
    }
}

pub(super) open spec fn recover_keys_from_mapping<K>(mapping: KeyRecoveryMapping<K>) -> KeyTableSnapshot<K>
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
    match KeyRecoveryMapping::<K>::new(s, sm) {
        None => None,
        Some(mapping) => Some(recover_keys_from_mapping::<K>(mapping)),
    }
}

}
