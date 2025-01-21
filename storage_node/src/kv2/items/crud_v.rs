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
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use recover_v::*;
use std::collections::HashSet;
use std::hash::Hash;
use super::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, I> ItemTable<PM, I>
    where
        PM: PersistentMemoryRegion,
        I: PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn read(&self, row_addr: u64, journal: &Journal<TrustedKvPermission, PM>) -> (result: Result<I, KvError>)
        requires
            journal.valid(),
            self.valid(journal@),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            match result {
                Ok(item) => self@.tentative.unwrap().m[row_addr] == item,
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        proof {
            self.lemma_valid_implications(journal@);
            broadcast use group_validate_row_addr;
        }

        match exec_recover_object::<PM, I>(journal.get_pm_region_ref(), row_addr + self.sm.row_item_start,
                                           row_addr + self.sm.row_item_crc_start) {
            Some(item) => Ok(item),
            None => Err(KvError::CRCMismatch),
        }
    }

    pub exec fn create(
        &mut self,
        item: &I,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative.is_some(),
            old(journal).valid(),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(item_addr) => {
                    &&& self@ == (ItemTableView {
                        tentative: Some(old(self)@.tentative.unwrap().create(item_addr, *item)),
                        ..old(self)@
                    })
                    &&& !old(self)@.tentative.unwrap().m.contains_key(item_addr)
                    &&& self.validate_item_addr(item_addr)
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ItemTableView {
                        tentative: None,
                        ..old(self)@
                    })
                }
                _ => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn delete(
        &mut self,
        item_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative.is_some(),
            old(self)@.tentative.unwrap().m.contains_key(item_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(_) => {
                    &&& self@ == (ItemTableView {
                        tentative: Some(old(self)@.tentative.unwrap().delete(item_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ItemTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

}

}

