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
use super::{ListSummary, ListTable, ListTableEntry, ListTableStaticMetadata};
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {

impl<Perm, PM, L> ListTable<Perm, PM, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn get_elements_case_durable(
        &self,
        list_addr: u64,
        summary: &ListSummary,
        journal: &Journal<Perm, PM>,
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Durable,
            summary == self.m@[list_addr]->Durable_summary,
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
        summary: &ListSummary,
        elements: &Vec<L>,
        journal: &Journal<Perm, PM>,
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative.is_some(),
            self@.tentative.unwrap().m.contains_key(list_addr),
            self.m@.contains_key(list_addr),
            self.m@[list_addr] is Modified,
            durable_head == self.m@[list_addr]->Modified_durable_head,
            summary == self.m@[list_addr]->Modified_summary,
            elements == self.m@[list_addr]->Modified_elements,
        ensures
            match result {
                Ok(elements) => elements@ == self.tentative_mapping@.list_elements[list_addr],
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        proof {
            broadcast use pmcopy_axioms;
        }

        if summary.length == elements.len() {
            assert(elements@ == self.tentative_mapping@.list_elements[list_addr]);
            return Ok(clone_pmcopy_vec(&elements));
        }

        let mut current_addr = list_addr;
        let mut result = Vec::<L>::new();
        let ghost durable_addrs = self.durable_mapping@.list_info[durable_head];
        let ghost durable_elements = self.durable_mapping@.list_elements[durable_head];
        let ghost tentative_addrs = self.tentative_mapping@.list_info[list_addr];
        let ghost tentative_elements = self.tentative_mapping@.list_elements[list_addr];
        let pm = journal.get_pm_region_ref();

        let num_durable_addrs = summary.length - elements.len();
        assert(tentative_elements.take(0) =~= Seq::<L>::empty());
        assert(tentative_addrs.take(num_durable_addrs as int) =~=
               durable_addrs.skip(durable_addrs.len() - num_durable_addrs));
        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        for current_pos in 0..num_durable_addrs
            invariant
                num_durable_addrs == summary.length - elements.len(),
                current_pos < num_durable_addrs ==> current_addr == tentative_addrs[current_pos as int],
                result@ == tentative_elements.take(current_pos as int),
                self.valid(journal@),
                journal.valid(),
                self.durable_mapping@.list_info.contains_key(durable_head),
                self.tentative_mapping@.list_info.contains_key(list_addr),
                0 < durable_addrs.len(),
                durable_addrs.len() == durable_elements.len(),
                elements.len() < summary.length,
                summary.length - elements.len() <= durable_elements.len(),
                durable_addrs == self.durable_mapping@.list_info[durable_head],
                durable_elements == self.durable_mapping@.list_elements[durable_head],
                tentative_addrs == self.tentative_mapping@.list_info[list_addr],
                tentative_elements == self.tentative_mapping@.list_elements[list_addr],
                tentative_addrs.take(num_durable_addrs as int) ==
                    durable_addrs.skip(durable_addrs.len() - num_durable_addrs),
                tentative_elements ==
                    durable_elements.skip(durable_elements.len() - (summary.length - elements.len())) + elements@,
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(tentative_elements.take(current_pos as int).push(tentative_elements[current_pos as int]) =~=
                   tentative_elements.take(current_pos + 1));

            let ghost which_durable_addr = durable_addrs.len() - num_durable_addrs + current_pos;
            assert(durable_addrs.skip(durable_addrs.len() - num_durable_addrs)[current_pos as int] ==
                   durable_addrs[which_durable_addr]);
            assert(current_addr == durable_addrs[which_durable_addr]);
            assert(0 <= which_durable_addr < durable_addrs.len());

            let element_addr = current_addr + self.sm.row_element_start;
            let element_crc_addr = current_addr + self.sm.row_element_crc_start;
            let current_element = match exec_recover_object::<PM, L>(pm, element_addr, element_crc_addr) {
                Some(e) => e,
                None => { return Err(KvError::CRCMismatch); },
            };

            result.push(current_element);

            // If this isn't the last durable element, read the
            // pointer to the next one from storage. (If it is the
            // last durable element, there's no point reading it since
            // we know it's 0 and we're not going to use it anyway.)

            if current_pos + 1 < num_durable_addrs {
                assert(durable_addrs.skip(durable_addrs.len() - num_durable_addrs)[current_pos + 1] =~=
                       durable_addrs[which_durable_addr + 1]);
                assert(durable_addrs[which_durable_addr + 1] =~= tentative_addrs[current_pos + 1]);
                let next_addr = current_addr + self.sm.row_next_start;
                let next_crc_addr = next_addr + size_of::<u64>() as u64;
                current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                    Some(n) => n,
                    None => { return Err(KvError::CRCMismatch); },
                };
            }
        }

        assert(tentative_elements == result@ + elements@) by {
            assert(tentative_elements =~= tentative_elements.take(summary.length - elements.len()) + elements@);
        }

        let mut elements_cloned = clone_pmcopy_vec(&elements);
        result.append(&mut elements_cloned);
        Ok(result)
    }

    pub exec fn read(
        &self,
        list_addr: u64,
        journal: &Journal<Perm, PM>
    ) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative is Some,
            self@.tentative.unwrap().m.contains_key(list_addr),
        ensures
            match result {
                Ok(lst) => self@.tentative.unwrap().m[list_addr] == lst@,
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
            Some(ListTableEntry::<L>::Durable{ ref summary }) =>
                self.get_elements_case_durable(list_addr, summary, journal),
            Some(ListTableEntry::<L>::Modified{ ref durable_head, ref summary, ref elements, .. }) =>
                self.get_elements_case_modified(list_addr, Ghost(durable_head@), summary, elements, journal),
        }
    }

    pub exec fn get_list_length(
        &self,
        list_addr: u64,
        journal: &Journal<Perm, PM>
    ) -> (result: Result<usize, KvError>)
        requires
            self.valid(journal@),
            journal.valid(),
            self@.tentative is Some,
            self@.tentative.unwrap().m.contains_key(list_addr),
        ensures
            match result {
                Ok(num_elements) => self@.tentative.unwrap().m[list_addr].len() == num_elements,
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
            Some(ListTableEntry::<L>::Durable{ ref summary }) => Ok(summary.length),
            Some(ListTableEntry::<L>::Modified{ ref summary, .. }) => Ok(summary.length),
        }
    }
}

}

