#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
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

    pub closed spec fn spec_setup_end(ps: SetupParameters, min_start: nat) -> nat
    {
        local_spec_setup_end::<K>(ps, min_start)
    }

    pub exec fn setup_end(ps: &SetupParameters, min_start: &OverflowingU64) -> (result: OverflowingU64)
        requires
            ps.valid(),
        ensures
            result@ == Self::spec_setup_end(*ps, min_start@),
            min_start@ <= result@,
    {
        local_setup_end::<K>(ps, min_start)
    }
    
    pub exec fn setup(
        pm: &mut PM,
        ps: &SetupParameters,
        min_start: u64,
        max_end: u64,
    ) -> (result: Result<KeyTableStaticMetadata, KvError<K>>)
        requires
            old(pm).inv(),
            ps.valid(),
            min_start <= max_end <= old(pm)@.len(),
            0 < K::spec_size_of(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            pm@.len() == old(pm)@.len(),
            match result {
                Ok(sm) => {
                    &&& Self::recover(pm@.read_state, sm) == Some(KeyTableSnapshot::<K>::init())
                    &&& seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int,
                                                 sm.table.end as int)
                    &&& sm.valid()
                    &&& sm.consistent_with_type::<K>()
                    &&& min_start <= sm.table.start
                    &&& sm.table.start <= sm.table.end
                    &&& sm.table.end <= max_end
                    &&& sm.table.end == Self::spec_setup_end(*ps, min_start as nat)
                    &&& sm.table.num_rows == ps.num_keys
                },
                Err(KvError::OutOfSpace) => max_end < Self::spec_setup_end(*ps, min_start as nat),
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
            sm.table.end <= s1.len(),
            seqs_match_in_range(s1, s2, sm.table.start as int, sm.table.end as int),
            Self::recover(s1, sm) is Some,
        ensures
            Self::recover(s1, sm) == Self::recover(s2, sm),
    {
        local_lemma_recover_depends_only_on_my_area::<K>(s1, s2, sm);
    }

}

}
