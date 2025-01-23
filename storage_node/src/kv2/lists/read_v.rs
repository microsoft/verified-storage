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
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn read(
        &mut self,
        row_addr: u64,
        journal: &Journal<TrustedKvPermission, PM>
    ) -> (result: Result<&[L], KvError>)
        requires
            old(self).valid(journal@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            self.valid(journal@),
            self@ == old(self)@,
            match result {
                Ok(lst) => self@.tentative.unwrap().m[row_addr] == lst@,
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn read_entry_at_index(
        &mut self,
        row_addr: u64,
        idx: u64,
        journal: &Journal<TrustedKvPermission, PM>
    ) -> (result: Result<&L, KvError>)
        requires
            old(self).valid(journal@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            self.valid(journal@),
            self@ == old(self)@,
            match result {
                Ok(element) => {
                    let elements = self@.tentative.unwrap().m[row_addr];
                    &&& idx < elements.len()
                    &&& element == elements[idx as int]
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    let elements = self@.tentative.unwrap().m[row_addr];
                    &&& idx >= elements.len()
                    &&& upper_bound == elements.len()
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

