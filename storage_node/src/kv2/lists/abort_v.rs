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
    pub exec fn abort(
        &mut self,
        jv_before_abort: Ghost<JournalView>,
        jv_after_abort: Ghost<JournalView>,
    )
        requires
            old(self).valid(jv_before_abort@),
            jv_before_abort@.valid(),
            jv_after_abort@.valid(),
            jv_after_abort == jv_before_abort@.abort(),
        ensures
            self.valid(jv_after_abort@),
            self@ == (ListTableView{ tentative: Some(old(self)@.durable), ..old(self)@ }),
    {
        // Play back the undo list from back to front
        assume(false); // unimplemented
    }
}

}

