#![allow(unused_imports)]
mod keyinv_v;
mod keyrecover_v;
mod keysetup_v;
mod keystart_v;

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use keyinv_v::*;
use keyrecover_v::*;
use keysetup_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::kvspec_t::*;

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct KeyTableRowMetadata
{
    pub item_addr: u64,
    pub list_addr: u64,
}

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
    table: TableMetadata,
    key_size: u64,
    row_cdb_start: u64,
    row_metadata_start: u64,
    row_metadata_end: u64,
    row_metadata_crc_start: u64,
    row_key_start: u64,
    row_key_end: u64,
    row_key_crc_start: u64,
}

impl KeyTableStaticMetadata
{
    pub closed spec fn valid<K>(self) -> bool
        where
            K: PmCopy,
    {
        &&& self.table.valid()
        &&& self.key_size > 0
        &&& self.key_size == K::spec_size_of()
        &&& self.table.start <= self.table.end
        &&& self.row_cdb_start + u64::spec_size_of() <= self.row_metadata_start
        &&& self.row_metadata_end - self.row_metadata_start == KeyTableRowMetadata::spec_size_of()
        &&& self.row_metadata_end <= self.row_metadata_crc_start
        &&& self.row_metadata_crc_start + u64::spec_size_of() <= self.row_key_start
        &&& self.row_key_start + self.key_size <= self.row_key_end
        &&& self.row_key_end <= self.row_key_crc_start
        &&& self.row_key_crc_start + u64::spec_size_of() <= self.table.row_size
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
    status: Ghost<KeyTableStatus>,
    m: HashMap<K, ConcreteKeyInfo>,
    free_list: Vec<u64>,
    pending_deallocations: Vec<u64>,
    memory_mapping: Ghost<KeyMemoryMapping<K>>,
    undo_records: Vec<KeyUndoRecord<K>>,
    phantom: Ghost<core::marker::PhantomData<PM>>,
}

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub closed spec fn valid(self, sm: KeyTableStaticMetadata, jv: JournalView) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv(sm, jv)
    }

    pub closed spec fn recover(
        s: Seq<u8>,
        sm: KeyTableStaticMetadata,
    ) -> Option<KeyTableSnapshot<K>>
    {
        match KeyRecoveryMapping::<K>::new(s, sm) {
            None => None,
            Some(mapping) => Some(Self::recover_keys_from_mapping(mapping)),
        }
    }

    pub closed spec fn spec_space_needed_for_setup(ps: SetupParameters, min_start: nat) -> nat
    {
        // let row_cdb_start = 0;
        let row_metadata_start = u64::spec_size_of();
        let row_metadata_end = row_metadata_start + KeyTableRowMetadata::spec_size_of();
        let row_metadata_crc_start = row_metadata_end;
        let row_metadata_crc_end = row_metadata_crc_start + u64::spec_size_of();
        let row_key_start = row_metadata_crc_end;
        let row_key_end = row_key_start + K::spec_size_of();
        let row_key_crc_start = row_key_end;
        let row_key_crc_end = row_key_crc_start + u64::spec_size_of();
        let row_size = row_key_crc_end;
        let num_rows = ps.num_keys;
        let table_size = num_rows * row_size;
        let initial_space =
            if min_start > u64::MAX { 0 } else {
                space_needed_for_alignment(min_start as int, u64::spec_size_of() as int)
            };
        (initial_space + table_size) as nat
    }

}

}
