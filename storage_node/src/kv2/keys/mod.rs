#![allow(unused_imports)]
mod abort_v;
mod commit_v;
mod crud_v;
mod inv_v;
mod recover_v;
mod setup_v;
mod spec_v;
mod start_v;

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
use crud_v::*;
use deps_hack::PmCopy;
use inv_v::*;
use recover_v::*;
use setup_v::*;
use spec_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::impl_t::*;
use super::spec_t::*;

verus! {

pub use spec_v::{KeyTableRowMetadata, KeyTableSnapshot, KeyTableView};

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
pub struct KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    status: Ghost<KeyTableStatus>,
    must_abort: Ghost<bool>,
    sm: KeyTableStaticMetadata,
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
    pub closed spec fn view(&self) -> KeyTableView<K>
    {
        KeyTableView{
            sm: self.sm,
            durable: self.internal_view().apply_undo_records(self.undo_records@, self.sm).unwrap().as_snapshot(),
            tentative: if self.must_abort@ { None } else { Some(self.internal_view().as_snapshot()) },
        }
    }
    
    pub closed spec fn valid(self, jv: JournalView) -> bool
    {
        &&& self.status@ is Quiescent
        &&& self.inv(jv)
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

    pub closed spec fn validate_key_addr(&self, addr: u64) -> bool
    {
        self.sm.table.validate_row_addr(addr)
    }

    pub closed spec fn key_corresponds_to_key_addr(&self, k: K, addr: u64) -> bool
    {
        self.m@.contains_key(k) && self.m@[k].row_addr == addr
    }

    pub open spec fn state_equivalent_for_me_specific(
        s: Seq<u8>,
        durable_state: Seq<u8>,
        constants: JournalConstants,
        sm: KeyTableStaticMetadata
    ) -> bool
    {
        &&& seqs_match_except_in_range(durable_state, s, sm.start() as int, sm.end() as int)
        &&& Journal::<TrustedKvPermission, PM>::recover(s) matches Some(j)
        &&& j.constants == constants
        &&& j.state == s
        &&& Self::recover(s, sm) == Self::recover(durable_state, sm)
    }

    pub open spec fn state_equivalent_for_me(&self, s: Seq<u8>, jv: JournalView) -> bool
    {
        Self::state_equivalent_for_me_specific(s, jv.durable_state, jv.constants, self@.sm)
    }
}

}
