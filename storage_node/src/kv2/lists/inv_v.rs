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

#[verifier::ext_equal]
pub(super) enum ListTableStatus {
    Quiescent,
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn inv(self, jv: JournalView) -> bool
    {
        arbitrary()
    }

    pub proof fn lemma_valid_implies_recover(self, jv: JournalView, list_addrs: Set<u64>)
        requires
            self.valid(jv),
            list_addrs.insert(0) == self@.durable.m.dom(),
        ensures
            Self::recover(jv.durable_state, list_addrs, self@.sm) == Some(self@.durable),
    {
        assume(false);
    }

    pub proof fn lemma_valid_implies_recover_after_commit(self, jv: JournalView, list_addrs: Set<u64>)
        requires
            self.valid(jv),
            self@.tentative is Some,
            list_addrs.insert(0) == self@.tentative.unwrap().m.dom(),
        ensures
            Self::recover(jv.commit_state, list_addrs, self@.sm) == self@.tentative,
    {
        assume(false);
    }
}

}

