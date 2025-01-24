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
    pub exec fn update(
        &mut self,
        row_addr: u64,
        idx: usize,
        new_list_entry: L,
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
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_row_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[row_addr];
                    &&& new_row_addr != 0
                    &&& new_row_addr == row_addr || !old(self)@.tentative.unwrap().m.contains_key(new_row_addr)
                    &&& idx < old_list.len()
                    &&& old_list[idx as int].start() == new_list_entry.start()
                    &&& old_list[idx as int].end() == new_list_entry.end()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_entry_at_index(row_addr, new_row_addr,
                                                                                          idx, new_list_entry)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_row_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    let old_list = old(self)@.tentative.unwrap().m[row_addr];
                    &&& self@ == old(self)@
                    &&& idx >= old_list.len()
                    &&& upper_bound == old_list.len()
                },
                Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end }) => {
                    let old_list = old(self)@.tentative.unwrap().m[row_addr];
                    &&& self@ == old(self)@
                    &&& idx < old_list.len()
                    &&& old_start == old_list[idx as int].start()
                    &&& old_end == old_list[idx as int].end()
                    &&& new_start == new_list_entry.start()
                    &&& new_end == new_list_entry.end()
                    &&& old_start != new_start || old_end != new_end
                }
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

