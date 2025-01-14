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
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub proof fn lemma_valid_depends_only_on_my_area(&self, old_jv: JournalView, new_jv: JournalView)
        requires
            self.valid(old_jv),
            old_jv.matches_in_range(new_jv, self@.sm.start() as int, self@.sm.end() as int),
        ensures
            self.valid(new_jv),
    {
        assume(false);
    }

    pub proof fn lemma_recover_depends_only_on_my_area(
        s1: Seq<u8>,
        s2: Seq<u8>,
        addrs: Set<u64>,
        sm: ListTableStaticMetadata,
    )
        requires
            sm.valid::<L>(),
            sm.end() <= s1.len(),
            seqs_match_in_range(s1, s2, sm.start() as int, sm.end() as int),
            Self::recover(s1, addrs, sm) is Some,
        ensures
            Self::recover(s1, addrs, sm) == Self::recover(s2, addrs, sm),
    {
        assume(false);
    }
}

}
