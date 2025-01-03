#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::table_v::*;
use crate::common::subrange_v::*;
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
    
    pub exec fn setup(
        pm: &mut PM,
        sm: &KeyTableStaticMetadata,
    )
        requires
            old(pm).inv(),
            sm.valid(),
            sm.consistent_with_type::<K>(),
            sm.table.end <= old(pm)@.len(),
        ensures
            pm.inv(),
            pm.constants() == old(pm).constants(),
            Self::recover(pm@.read_state, *sm) == Some(KeyTableSnapshot::<K>::init()),
            seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
    {
        exec_setup::<PM, K>(pm, sm)
    }
}

}
