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

    pub proof fn lemma_valid_implications(self, jv: JournalView)
        requires
            self.valid(jv),
        ensures
            self@.durable.m.contains_key(0),
            self@.durable.m[0] == Seq::<L>::empty(),
            Self::recover(jv.durable_state, self@.durable.m.dom(), self@.sm) == Some(self@.durable),
            self@.tentative is Some ==> {
                let tentative = self@.tentative.unwrap();
                &&& tentative.m.contains_key(0)
                &&& tentative.m[0] == Seq::<L>::empty()
                &&& Self::recover(jv.commit_state, tentative.m.dom(), self@.sm) == self@.tentative
            },
    {
        assume(false);
    }
}

}

