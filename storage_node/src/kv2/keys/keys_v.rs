#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::overflow_v::*;
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
use super::keyrecover_v::*;
use super::keysetup_v::*;
use super::super::kvspec_t::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableSnapshot<K>
{
    pub key_info: Map<K, KeyTableRowMetadata>,
    pub item_info: Map<u64, K>,
    pub list_info: Map<u64, K>,
}

impl<K> KeyTableSnapshot<K>
{
    pub open spec fn init() -> Self
    {
        Self{
            key_info: Map::<K, KeyTableRowMetadata>::empty(),
            item_info: Map::<u64, K>::empty(),
            list_info: Map::<u64, K>::empty(),
        }
    }

    pub open spec fn key_info_valid(self) -> bool
    {
        &&& forall|k: K| #[trigger] self.key_info.contains_key(k) ==> {
            let rm = self.key_info[k];
            &&& self.item_info.contains_key(rm.item_addr)
            &&& self.item_info[rm.item_addr] == k
            &&& self.list_info.contains_key(rm.list_addr)
            &&& self.list_info[rm.list_addr] == k
        }
    }

    pub open spec fn item_info_valid(self) -> bool
    {
        &&& forall|addr: u64| #[trigger] self.item_info.contains_key(addr) ==> {
            let k = self.item_info[addr];
            &&& self.key_info.contains_key(k)
            &&& self.key_info[k].item_addr == addr
        }
    }

    pub open spec fn list_info_valid(self) -> bool
    {
        &&& forall|addr: u64| #[trigger] self.list_info.contains_key(addr) ==> {
            let k = self.list_info[addr];
            &&& self.key_info.contains_key(k)
            &&& self.key_info[k].list_addr == addr
        }
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.key_info_valid()
        &&& self.item_info_valid()
        &&& self.list_info_valid()
    }

    pub open spec fn item_addrs(self) -> Set<u64>
    {
        self.item_info.dom()
    }

    pub open spec fn list_addrs(self) -> Set<u64>
    {
        self.list_info.dom()
    }
}

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyTableStaticMetadata
{
    pub(super) table: TableMetadata,
    pub(super) key_size: u64,
    pub(super) row_cdb_start: u64,
    pub(super) row_metadata_start: u64,
    pub(super) row_metadata_end: u64,
    pub(super) row_metadata_crc_start: u64,
    pub(super) row_key_start: u64,
    pub(super) row_key_end: u64,
    pub(super) row_key_crc_start: u64,
}

impl KeyTableStaticMetadata
{
    pub(super) open spec fn valid_internal(self) -> bool
    {
        &&& self.table.valid()
        &&& self.key_size > 0
        &&& self.table.start <= self.table.end
        &&& self.row_cdb_start + u64::spec_size_of() <= self.row_metadata_start
        &&& self.row_metadata_end - self.row_metadata_start == KeyTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_metadata_crc_start
        &&& self.row_metadata_crc_start + u64::spec_size_of() <= self.row_key_start
        &&& self.row_key_start + self.key_size <= self.row_key_end
        &&& self.row_key_end <= self.row_key_crc_start
        &&& self.row_key_crc_start + u64::spec_size_of() <= self.table.row_size
    }

    pub closed spec fn valid(self) -> bool
    {
        self.valid_internal()
    }

    pub closed spec fn consistent_with_type<K>(self) -> bool
        where
            K: PmCopy,
    {
        self.key_size == K::spec_size_of()
    }

    pub closed spec fn spec_start(self) -> u64
    {
        self.table.start
    }

    #[verifier::when_used_as_spec(spec_start)]
    pub exec fn start(self) -> (result: u64)
        ensures
            result == self.spec_start(),
    {
        self.table.start
    }

    pub closed spec fn spec_end(self) -> u64
    {
        self.table.end
    }

    #[verifier::when_used_as_spec(spec_end)]
    pub exec fn end(self) -> (result: u64)
        ensures
            result == self.spec_end(),
    {
        self.table.end
    }

    pub closed spec fn num_rows(self) -> u64
    {
        self.table.num_rows
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableView<K>
{
    pub durable: KeyTableSnapshot<K>,
    pub tentative: KeyTableSnapshot<K>,
}
    
#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    m: HashMap<K, u64>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub closed spec fn recover(
        s: Seq<u8>,
        sm: KeyTableStaticMetadata,
    ) -> Option<KeyTableSnapshot<K>>
    {
        recover_keys(s, sm)
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        local_spec_space_needed_for_setup::<K>(ps, min_start)
    }

    pub exec fn space_needed_for_setup(ps: &SetupParameters, min_start: &OverflowingU64) -> (result: OverflowingU64)
        requires
            ps.valid(),
        ensures
            result@ == Self::spec_space_needed_for_setup(*ps, min_start@),
    {
        local_space_needed_for_setup::<K>(ps, min_start)
    }
    
    pub exec fn setup(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<KeyTableStaticMetadata, KvError<K>>)
        requires
            old(pm).inv(),
            old(pm)@.valid(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.valid(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, sm) == Some(KeyTableSnapshot::<K>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.start() as int,
                                                 sm.end() as int)
                    &&& sm.valid()
                    &&& sm.consistent_with_type::<K>()
                    &&& min_start <= sm.start() <= sm.end() <= max_end
                    &&& sm.end() - min_start == Self::spec_space_needed_for_setup(*ps, min_start as nat)
                    &&& sm.num_rows() == ps.num_keys
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(KvError::OutOfSpace) =>
                    max_end - min_start < Self::spec_space_needed_for_setup(*ps, min_start as nat),
                _ => false,
            },
    {
        exec_setup::<PM, K>(pm, ps, min_start, max_end)
    }

    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        sm: KeyTableStaticMetadata,
    )
        requires
            sm.valid(),
            sm.consistent_with_type::<K>(),
            sm.end() <= s1.len(),
            seqs_match_in_range(s1, s2, sm.start() as int, sm.end() as int),
            Self::recover(s1, sm) is Some,
        ensures
            Self::recover(s1, sm) == Self::recover(s2, sm),
    {
        local_lemma_recover_depends_only_on_my_area::<K>(s1, s2, sm);
    }

}

}
