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
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, K> KeyTable<PM, K>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
{
    pub exec fn commit(
        &mut self,
        jv_before_commit: Ghost<JournalView>,
        jv_after_commit: Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_commit@),
            old(self)@.tentative is Some,
            jv_before_commit@.valid(),
            jv_after_commit@.valid(),
            jv_after_commit@.committed_from(jv_before_commit@),
        ensures
            self.valid(jv_after_commit@),
            self@ == (KeyTableView{ durable: old(self)@.tentative.unwrap(), ..old(self)@ }),
    {
        // Play back the undo list from back to front
        assume(false); // unimplemented
    }
}

}

