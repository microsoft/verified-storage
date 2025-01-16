#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
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
use super::*;
use super::recover_v::*;
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn read(&self, k: &K, jv: Ghost<JournalView>) -> (result: Option<(u64, KeyTableRowMetadata)>)
        requires
            self.valid(jv@),
            self@.tentative.is_some(),
        ensures
            match result {
                None => !self@.tentative.unwrap().key_info.contains_key(*k),
                Some((key_addr, rm)) => {
                    let tentative = self@.tentative.unwrap();
                    &&& tentative.key_info.contains_key(*k)
                    &&& tentative.key_info[*k] == rm
                    &&& self.key_corresponds_to_key_addr(*k, key_addr)
                },
            }
    {
        match self.m.get(k) {
            None => None,
            Some(concrete_key_info) => Some((concrete_key_info.row_addr, concrete_key_info.rm)),
        }
    }

    pub exec fn create(
        &mut self,
        k: &K,
        item_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create(*k, item_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn delete(
        &mut self,
        k: &K,
        key_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().delete(*k)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_item(
        &mut self,
        k: &K,
        key_addr: u64,
        item_addr: u64,
        current_list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            old(self)@.tentative.unwrap().key_info[*k].list_addr == current_list_addr,
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_item(*k, item_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_list(
        &mut self,
        k: &K,
        key_addr: u64,
        current_item_addr: u64,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            old(self)@.tentative.unwrap().key_info[*k].item_addr == current_item_addr,
            !old(self)@.tentative.unwrap().list_addrs().contains(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_list(*k, list_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn update_item_and_list(
        &mut self,
        k: &K,
        key_addr: u64,
        item_addr: u64,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().key_info.contains_key(*k),
            old(self).key_corresponds_to_key_addr(*k, key_addr),
            !old(self)@.tentative.unwrap().item_addrs().contains(item_addr),
            !old(self)@.tentative.unwrap().list_addrs().contains(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(()) => {
                    &&& self@ == (KeyTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_item_and_list(*k, item_addr, list_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (KeyTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

