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
use vstd::std_specs::hash::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn get_row_addrs_case_durable(
        &self,
        list_addr: u64,
        entry: &ListTableDurableEntry,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<u64>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Durable,
            entry == self.m@[list_addr]->Durable_entry,
        ensures
            match result {
                Ok(addrs) => addrs@ == self.tentative_mapping@.list_info[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result = Vec::<u64>::new();
        let ghost current_pos: int = 0;
        let ghost addrs = self.durable_mapping@.list_info[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(addrs.take(current_pos) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }
        
        while current_addr != 0
            invariant
                0 <= current_pos <= addrs.len(),
                current_pos == addrs.len() <==> current_addr == 0,
                current_pos < addrs.len() ==> current_addr == addrs[current_pos],
                result@ == addrs.take(current_pos),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(list_addr),
                addrs == self.durable_mapping@.list_info[list_addr],
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
            decreases
                addrs.len() - result@.len(),
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(addrs.take(current_pos).push(current_addr) =~= addrs.take(current_pos + 1));
            result.push(current_addr);

            let next_addr = current_addr + self.sm.row_next_start;
            let next_crc_addr = next_addr + size_of::<u64>() as u64;
            current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                Some(n) => n,
                None => { return Err(KvError::CRCMismatch); },
            };
            proof {
                current_pos = current_pos + 1;
            }
        }
        
        assert(addrs.take(current_pos) =~= addrs);
        assert(self.tentative_mapping@.list_info[list_addr] == self.durable_mapping@.list_info[list_addr]);
        Ok(result)
    }

    exec fn get_row_addrs_case_modified(
        &self,
        list_addr: u64,
        entry: &ListTableDurableEntry,
        addrs: &Vec<u64>,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<u64>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Modified,
            entry == self.m@[list_addr]->Modified_entry,
            addrs == self.m@[list_addr]->Modified_addrs,
        ensures
            match result {
                Ok(addrs) => addrs@ == self.tentative_mapping@.list_info[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        if entry.length == addrs.len() {
            return Ok(addrs.clone());
        }

        assume(false);
        Err(KvError::NotImplemented)
        /*

        let mut current_addr = list_addr;
        let mut result = Vec::<u64>::new();
        let mut current_pos: usize = 0;
        let ghost durable_addrs = self.durable_mapping@.list_info[list_addr];
        let ghost tentative_addrs = self.tentative_mapping@.list_info[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(tentative_addrs.take(current_pos as int) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        let num_durable_addrs = entry.length - addrs.len();
        while current_pos < num_durable_addrs
            invariant
                0 <= current_pos <= durable.length - num_trimmed,
                current_addr == tentative_addrs[current_pos as int],
                result@ == tentative_addrs.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(list_addr),
                self.tentative_mapping@.list_info.contains_key(list_addr),
                tentative_addrs == self.tentative_mapping@.list_info[list_addr],
                durable_addrs.skip(num_trimmed as int) == tentative_addrs.take(durable.length - num_trimmed),
                appended_addrs@ == tentative_addrs.skip(durable.length - num_trimmed),
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
            decreases
                tentative_addrs.len() - result@.len(),
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(tentative_addrs.take(current_pos as int).push(current_addr) =~=
                   tentative_addrs.take(current_pos + 1));
            result.push(current_addr);

            let next_addr = current_addr + self.sm.row_next_start;
            let next_crc_addr = next_addr + size_of::<u64>() as u64;
            current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                Some(n) => n,
                None => { return Err(KvError::CRCMismatch); },
            };

            current_pos = current_pos + 1;
        }

        let num_appended_addrs = appended_addrs.len();
        while current_pos < num_appended_addrs
            invariant
                durable.length <= current_pos <= num_appended_addrs == appended_addrs.len(),
                appended_addrs@ == self.tentative_mapping@.list_info[list_addr].skip(durable.length as int),
                result@ == tentative_addrs.take(current_pos as int),
        {
            assert(tentative_addrs.take(current_pos as int).push(appended_addrs@[num_appended_addrs - current_pos])
                   =~= tentative_addrs.take(current_pos + 1));
            result.push(appended_addrs[num_appended_addrs - current_pos]);
            current_pos = current_pos + 1;
        }

        assert(tentative_addrs.take(current_pos as int) =~= tentative_addrs);
        Ok(result)
        */
    }

    exec fn get_row_addrs(
        &self,
        list_addr: u64,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<u64>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
        ensures
            match result {
                Ok(addrs) => addrs@ == self.tentative_mapping@.list_info[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        proof {
            broadcast use group_hash_axioms;
        }

        match self.m.get(&list_addr) {
            None => {
                assert(false);
                Err(KvError::InternalError)
            },
            Some(ListTableEntry::<L>::Durable{ ref entry }) =>
                self.get_row_addrs_case_durable(list_addr, entry, journal),
            Some(ListTableEntry::<L>::Modified{ ref entry, ref addrs, .. }) =>
                self.get_row_addrs_case_modified(list_addr, entry, addrs, journal),
        }
    }

    pub exec fn delete(
        &mut self,
        list_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative.is_some(),
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(_) => {
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().delete(list_addr)),
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
                Err(KvError::OutOfSpace) => {
                    &&& self@ == (ListTableView {
                        tentative: None,
                        ..old(self)@
                    })
                },
                _ => false,
            }
    {
        proof {
            broadcast use group_hash_axioms;
        }

        assume(false);
        return Err(KvError::NotImplemented);
    }
}

}

