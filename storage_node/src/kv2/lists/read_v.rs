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
use vstd::std_specs::hash::*;

verus! {

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn get_elements_case_durable(
        &self,
        list_addr: u64,
        entry: &ListTableDurableEntry,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<L>, KvError>)
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
                Ok(elements) => elements@ == self.tentative_mapping@.list_elements[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result = Vec::<L>::new();
        let ghost current_pos: int = 0;
        let ghost addrs = self.durable_mapping@.list_info[list_addr];
        let ghost elements = self.durable_mapping@.list_elements[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(elements.take(current_pos) =~= Seq::<L>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }
        
        while current_addr != 0
            invariant
                0 <= current_pos <= addrs.len(),
                current_pos == addrs.len() <==> current_addr == 0,
                addrs.len() == elements.len(),
                current_pos < addrs.len() ==> current_addr == addrs[current_pos],
                result@ == elements.take(current_pos),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(list_addr),
                addrs == self.durable_mapping@.list_info[list_addr],
                elements == self.durable_mapping@.list_elements[list_addr],
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

            assert(elements.take(current_pos).push(elements[current_pos as int]) =~= elements.take(current_pos + 1));

            let element_addr = current_addr + self.sm.row_element_start;
            let element_crc_addr = current_addr + self.sm.row_element_crc_start;
            let current_element = match exec_recover_object::<PM, L>(pm, element_addr, element_crc_addr) {
                Some(e) => e,
                None => { return Err(KvError::CRCMismatch); },
            };

            result.push(current_element);

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
        
        assert(elements.take(current_pos) =~= elements);
        assert(self.tentative_mapping@.list_elements[list_addr] == self.durable_mapping@.list_elements[list_addr]);
        Ok(result)
    }

    exec fn get_elements_case_modified(
        &self,
        list_addr: u64,
        Ghost(durable_head): Ghost<u64>,
        entry: &ListTableDurableEntry,
        elements: &Vec<L>,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Modified,
            durable_head == self.m@[list_addr]->Modified_durable_head,
            entry == self.m@[list_addr]->Modified_entry,
            elements == self.m@[list_addr]->Modified_elements,
        ensures
            match result {
                Ok(elements) => elements@ == self.tentative_mapping@.list_elements[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    /*
        if entry.length == addrs.len() {
            return Ok(addrs.clone());
        }

        let mut current_addr = list_addr;
        let mut result = Vec::<u64>::new();
        let mut current_pos: usize = 0;
        let ghost durable_addrs = self.durable_mapping@.list_info[durable_head];
        let ghost tentative_addrs = self.tentative_mapping@.list_info[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(tentative_addrs.take(current_pos as int) =~= Seq::<u64>::empty());
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        let num_durable_addrs = entry.length - addrs.len();
        while current_pos < num_durable_addrs
            invariant
                num_durable_addrs == entry.length - addrs.len(),
                0 <= current_pos <= num_durable_addrs,
                current_pos < num_durable_addrs ==> current_addr == tentative_addrs[current_pos as int],
                result@ == tentative_addrs.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(durable_head),
                self.tentative_mapping@.list_info.contains_key(list_addr),
                0 < durable_addrs.len(),
                addrs.len() < entry.length,
                entry.length - addrs.len() <= durable_addrs.len(),
                durable_addrs == self.durable_mapping@.list_info[durable_head],
                tentative_addrs == self.tentative_mapping@.list_info[list_addr],
                tentative_addrs == durable_addrs.skip(durable_addrs.len() - (entry.length - addrs.len())) + addrs@,
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
            decreases
                num_durable_addrs - current_pos,
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

        assert(tentative_addrs == result@ + addrs@) by {
            assert(tentative_addrs =~= tentative_addrs.take(entry.length - addrs.len()) + addrs@);
        }

        let mut addrs_cloned = addrs.clone();
        result.append(&mut addrs_cloned);
        Ok(result)
    */
    }

    exec fn get_elements(
        &self,
        list_addr: u64,
        journal: &Journal<TrustedKvPermission, PM>,
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
        ensures
            match result {
                Ok(elements) => elements@ == self.tentative_mapping@.list_elements[list_addr],
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
                self.get_elements_case_durable(list_addr, entry, journal),
            Some(ListTableEntry::<L>::Modified{ ref durable_head, ref entry, ref elements, .. }) =>
                self.get_elements_case_modified(list_addr, Ghost(durable_head@), entry, elements, journal),
        }
    }

    pub exec fn read(
        &mut self,
        row_addr: u64,
        journal: &Journal<TrustedKvPermission, PM>
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            old(self).valid(journal@),
            journal.valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(row_addr),
        ensures
            self.valid(journal@),
            self@ == old(self)@,
            match result {
                Ok(lst) => self@.tentative.unwrap().m[row_addr] == lst@,
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }
}

}

