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
impl<L> ListRecoveryMapping<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn delete(self, list_addr: u64) -> Self
        recommends
            self.list_info.contains_key(list_addr),
    {
        let new_row_info = Map::<u64, ListRowRecoveryInfo<L>>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr) && self.row_info[row_addr].head != list_addr,
            |row_addr: u64| self.row_info[row_addr],
        );
        Self{
            row_info: new_row_info,
            list_info: self.list_info.remove(list_addr),
            list_elements: self.list_elements.remove(list_addr),
        }
    }
}

impl ListRowDisposition
{
    pub(super) open spec fn add_to_pending_deallocations(self, dealloc_pos: nat) -> Self
    {
        match self {
            ListRowDisposition::NowhereFree =>
                ListRowDisposition::InPendingDeallocationList{ pos: dealloc_pos },
            ListRowDisposition::InPendingAllocationList{ pos } =>
                ListRowDisposition::InBothPendingLists{ alloc_pos: pos, dealloc_pos: dealloc_pos },
            _ => self,
        }
    }
}

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) open spec fn delete(self, list_addr: u64) -> Self
        recommends
            self.m.contains_key(list_addr),
    {
        let new_row_info = Map::<u64, ListRowDisposition>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr),
            |row_addr: u64|
                if {
                    &&& self.tentative_mapping.row_info.contains_key(row_addr)
                    &&& self.tentative_mapping.row_info[row_addr].head == list_addr
                } {
                    self.row_info[row_addr].add_to_pending_deallocations(
                        self.pending_deallocations.len() + self.tentative_mapping.row_info[row_addr].pos as nat
                    )
                } else {
                    self.row_info[row_addr]
                },
        );
        let new_deletes =
            if let ListTableEntryView::Durable{ entry } = self.m[list_addr] {
                self.deletes.push(entry)
            }
            else {
                self.deletes
            };
        let new_deletes_inverse =
            if self.m[list_addr] is Durable {
                self.deletes_inverse.insert(list_addr, self.deletes.len())
            }
            else {
                self.deletes_inverse
            };
        let new_modifications =
            if let ListTableEntryView::Modified{ which_modification, .. } = self.m[list_addr] {
                self.modifications.update(which_modification as int, None)
            }
            else {
                self.modifications
            };
        Self{
            tentative_list_addrs: self.tentative_list_addrs.remove(list_addr),
            tentative_mapping: self.tentative_mapping.delete(list_addr),
            row_info: new_row_info,
            m: self.m.remove(list_addr),
            deletes_inverse: new_deletes_inverse,
            deletes: new_deletes,
            modifications: new_modifications,
            pending_deallocations: self.pending_deallocations + self.tentative_mapping.list_info[list_addr],
            ..self
        }
    }

    pub(super) proof fn lemma_delete_works(
        self,
        list_addr: u64,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.valid(sm),
            0 < sm.start(),
            self.durable_mapping.internally_consistent(sm),
            self.tentative_mapping.internally_consistent(sm),
            self.m.contains_key(list_addr),
        ensures
            self.delete(list_addr).valid(sm),
            self.delete(list_addr).tentative_mapping.as_snapshot() ==
                self.tentative_mapping.as_snapshot().delete(list_addr),
    {
        let new_self = self.delete(list_addr);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();

        assert(new_snapshot =~= old_snapshot.delete(list_addr));

        assert(self.delete(list_addr).tentative_mapping.as_snapshot() =~=
               self.tentative_mapping.as_snapshot().delete(list_addr));
    }
}

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
        Ghost(durable_head): Ghost<u64>,
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
            durable_head == self.m@[list_addr]->Modified_durable_head,
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
            Some(ListTableEntry::<L>::Modified{ ref durable_head, ref entry, ref addrs, .. }) =>
                self.get_row_addrs_case_modified(list_addr, Ghost(durable_head@), entry, addrs, journal),
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
            self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            broadcast use group_hash_axioms;
        }

        let mut row_addrs = match self.get_row_addrs(list_addr, journal) {
            Ok(addrs) => addrs,
            Err(KvError::CRCMismatch) => {
                self.must_abort = Ghost(true);
                return Err(KvError::CRCMismatch);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost old_iv = self.internal_view();
        let ghost new_iv = old_iv.delete(list_addr);

        let table_entry = match self.m.remove(&list_addr) {
            Some(e) => e,
            None => { assert(false); return Err(KvError::InternalError); },
        };

        match table_entry {
            ListTableEntry::Durable{ entry } => {
                self.deletes.push(entry);
            },
            ListTableEntry::Modified{ which_modification, .. } => {
                self.modifications.set(which_modification, None);
            },
        }

        self.tentative_list_addrs = Ghost(new_iv.tentative_list_addrs);
        self.tentative_mapping = Ghost(new_iv.tentative_mapping);
        self.row_info = Ghost(new_iv.row_info);
        self.deletes_inverse = Ghost(new_iv.deletes_inverse);
        self.pending_deallocations.append(&mut row_addrs);

        proof {
            assert(self.internal_view() =~= new_iv);
            old_iv.lemma_delete_works(list_addr, self.sm);
        }

        Ok(())
    }
}

}

