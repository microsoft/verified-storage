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
    pub exec fn trim(
        &mut self,
        row_addr: u64,
        trim_length: usize,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[row_addr];
                    &&& {
                           ||| new_row_addr == 0
                           ||| new_row_addr == row_addr
                           ||| !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    }
                    &&& trim_length <= old_list.len()
                    &&& new_row_addr == 0 ==> old_list.skip(trim_length as int) == Seq::<L>::empty()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().trim(row_addr, new_row_addr, trim_length)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    &&& self@ == old(self)@
                    &&& trim_length > upper_bound
                    &&& upper_bound == old(self)@.tentative.unwrap().m[row_addr].len()
                },
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                Err(KvError::CRCMismatch) => {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self@ == (ListTableView {
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

