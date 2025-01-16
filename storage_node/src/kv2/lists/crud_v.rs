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
use super::spec_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub exec fn delete(
        &mut self,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(self)@.tentative.is_some(),
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            list_addr != 0,
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal.recover_idempotent(),
            journal@.constants_match(old(journal)@),
            old(journal)@.matches_except_in_range(journal@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(_) => {
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().delete(list_addr)),
                        ..old(self)@
                    })
                },
                Err(KvError::OutOfSpace) => {
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

