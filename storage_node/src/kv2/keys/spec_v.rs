#![allow(unused_imports)]
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
use inv_v::*;
use recover_v::*;
use setup_v::*;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

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
            &&& rm.list_addr != 0 ==> self.list_info.contains_key(rm.list_addr)
            &&& rm.list_addr != 0 ==> self.list_info[rm.list_addr] == k
        }
    }

    pub open spec fn item_info_valid(self) -> bool
    {
        &&& forall|addr: u64| #![trigger self.key_info.contains_key(self.item_info[addr])]
               self.item_info.contains_key(addr) ==> {
                   let k = self.item_info[addr];
                   &&& self.key_info.contains_key(k)
                   &&& self.key_info[k].item_addr == addr
               }
    }

    pub open spec fn list_info_valid(self) -> bool
    {
        &&& !self.list_info.contains_key(0)
        &&& forall|addr: u64| #![trigger self.key_info.contains_key(self.list_info[addr])]
               self.list_info.contains_key(addr) ==> {
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
        Set::<u64>::new(|item_addr: u64| self.item_info.contains_key(item_addr) &&
                                         self.key_info.contains_key(self.item_info[item_addr]))
    }

    pub open spec fn list_addrs(self) -> Set<u64>
    {
        Set::<u64>::new(|list_addr: u64| self.list_info.contains_key(list_addr) &&
                                         self.key_info.contains_key(self.list_info[list_addr]))
    }

    pub open spec fn create(self, k: K, item_addr: u64) -> Self
    {
        let rm = KeyTableRowMetadata{
            item_addr,
            list_addr: 0,
        };
        Self{
            key_info: self.key_info.insert(k, rm),
            item_info: self.item_info.insert(item_addr, k),
            list_info: self.list_info,
        }
    }

    pub open spec fn delete(self, k: K) -> Self
    {
        let rm = self.key_info[k];
        let new_list_info = if rm.list_addr == 0 {
            self.list_info
        } else {
            self.list_info.remove(rm.list_addr)
        };
        Self{
            key_info: self.key_info.remove(k),
            item_info: self.item_info.remove(rm.item_addr),
            list_info: new_list_info,
        }
    }

    pub open spec fn update(self, k: K, new_rm: KeyTableRowMetadata, former_rm: KeyTableRowMetadata) -> Self
    {
        let list_info_after_remove =
            if former_rm.list_addr != 0 {
                self.list_info.remove(former_rm.list_addr)
            }
            else {
                self.list_info
            };
        let new_list_info =
            if new_rm.list_addr != 0 {
                list_info_after_remove.insert(new_rm.list_addr, k)
            }
            else {
                list_info_after_remove
            };
        Self{
            key_info: self.key_info.insert(k, new_rm),
            item_info: self.item_info.remove(former_rm.item_addr).insert(new_rm.item_addr, k),
            list_info: new_list_info,
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::ext_equal]
pub struct KeyTableView<K>
{
    pub sm: KeyTableStaticMetadata,
    pub durable: KeyTableSnapshot<K>,
    pub tentative: Option<KeyTableSnapshot<K>>, // None if, due to an error like journal overflow, we must abort
}

}

