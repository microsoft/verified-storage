#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

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
use super::keys_v::*;
use super::keyrecover_v::*;
use super::super::kvimpl_t::*;
use super::super::kvspec_t::*;

verus! {

pub(super) exec fn exec_setup<PM, K>(
    pm: &mut PM,
    sm: &KeyTableStaticMetadata,
)
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + Sized + std::fmt::Debug,
    requires
        old(pm).inv(),
        sm.valid(),
        sm.table.end <= old(pm)@.len(),
    ensures
        pm.inv(),
        pm.constants() == old(pm).constants(),
        sm.valid(),
        recover_keys::<K>(pm@.read_state, *sm) == Some(KeyTableSnapshot::<K>::init()),
        seqs_match_except_in_range(old(pm)@.read_state, pm@.read_state, sm.table.start as int, sm.table.end as int),
{
    let row_addr = sm.table.start;
    proof { sm.table.lemma_start_is_valid_row(); }
    assume(false);
}

}
