#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
#[cfg(verus_keep_ghost)]
use util_v::lemma_writing_element_and_next_effect_on_recovery;
#[cfg(verus_keep_ghost)]
use util_v::lemma_writing_next_and_crc_together_effect_on_recovery;
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
use super::util_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::*;

verus! {
    
impl<L> ListTableEntry<L>
    where
        L: LogicalRange + PmCopy + std::fmt::Debug,
{
    // TODO - Do in place somehow
    exec fn update(self, idx: usize, new_row_addr: u64, new_element: L) -> (result: Self)
        requires
            match self {
                ListTableEntry::Modified{ summary, addrs, elements, .. } => {
                    &&& summary.length == addrs.len()
                    &&& addrs.len() == elements.len()
                    &&& idx < summary.length
                },
                _ => false,
            },
        ensures
            result@ == match self@ {
                ListTableEntryView::Modified{ which_modification, summary, durable_head, addrs, elements } =>
                    ListTableEntryView::Modified{
                        which_modification,
                        summary: ListSummary{
                            head: if idx == 0 { new_row_addr } else { summary.head },
                            tail: if idx == addrs.len() - 1 { new_row_addr } else { summary.tail },
                            ..summary
                        },
                        durable_head,
                        addrs: addrs.update(idx as int, new_row_addr),
                        elements: elements.update(idx as int, new_element)
                    },
                _ => self@,
            }
    {
        match self {
            ListTableEntry::Durable{ summary } => ListTableEntry::Durable{ summary },
            ListTableEntry::Modified{ which_modification, mut summary, durable_head, mut addrs, mut elements } => {
                addrs.set(idx, new_row_addr);
                elements.set(idx, new_element);
                if idx == 0 {
                    summary.head = new_row_addr;
                }
                if idx == addrs.len() - 1 {
                    summary.tail = new_row_addr;
                }
                ListTableEntry::Modified{ which_modification, summary, durable_head, addrs, elements }
            },
        }
    }
}
    
impl<L> ListTableInternalView<L>
    where
        L: LogicalRange + PmCopy + std::fmt::Debug,
{
    pub(super) open spec fn complete_entry(self, list_addr: u64) -> Self
        recommends
            self.m.contains_key(list_addr),
    {
        match self.m[list_addr] {
            ListTableEntryView::Durable{ summary } => {
                let addrs = self.durable_mapping.list_info[list_addr];
                let elements = self.durable_mapping.list_elements[list_addr];
                let which_delete = self.deletes.len();
                let which_modification = self.modifications.len();
                let new_entry =
                    ListTableEntryView::Modified{ which_modification, durable_head: 0, summary, addrs, elements };
                let which_delete = self.deletes.len();
                Self{
                    deletes_inverse: self.deletes_inverse.insert(list_addr, which_delete),
                    deletes: self.deletes.push(summary),
                    modifications: self.modifications.push(Some(list_addr)),
                    m: self.m.insert(list_addr, new_entry),
                    ..self
                }
            },
            ListTableEntryView::Modified{ which_modification, durable_head, summary, addrs, elements } => {
                let tentative_addrs = self.tentative_mapping.list_info[list_addr];
                let tentative_elements = self.tentative_mapping.list_elements[list_addr];
                let new_entry = ListTableEntryView::Modified{ which_modification, durable_head: 0, summary,
                                                              addrs: tentative_addrs, elements: tentative_elements };
                Self{
                    m: self.m.insert(list_addr, new_entry),
                    ..self
                }
            },
        }
    }

    proof fn lemma_complete_entry_maintains_correspondence(
        self,
        list_addr: u64,
        jv: JournalView,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            0 < sm.start(),
            sm.corresponds_to_journal(jv),
            self.corresponds_to_journal(jv, sm),
            self.tentative_mapping.list_info.contains_key(list_addr),
        ensures
            self.complete_entry(list_addr).corresponds_to_journal(jv, sm),
    {
    }

    pub(super) open spec fn update(self, list_addr: u64, idx: usize, new_element: L) -> Self
    {
        let new_row_addr = self.free_list.last();
        let old_addrs = self.tentative_mapping.list_info[list_addr];
        let new_addrs = old_addrs.update(idx as int, new_row_addr);
        let new_head = if idx == 0 { new_row_addr } else { list_addr };
        let old_row_addr = old_addrs[idx as int];

        let old_elements = self.tentative_mapping.list_elements[list_addr];
        let new_elements = old_elements.update(idx as int, new_element);

        let next_addr = if idx == old_addrs.len() - 1 { 0 } else { old_addrs[idx + 1] };
        let prev_addr = if idx == 0 { 0 } else { old_addrs[idx - 1] };

        let new_row_info = Map::<u64, ListRowRecoveryInfo<L>>::new(
            |row_addr: u64| {
                ||| row_addr == new_row_addr
                ||| {
                       &&& self.tentative_mapping.row_info.contains_key(row_addr)
                       &&& row_addr != old_row_addr
                }
            },
            |row_addr: u64|
            {
                if row_addr == new_row_addr {
                    ListRowRecoveryInfo::<L>{ element: new_element, head: new_head, next: next_addr, pos: idx as int }
                }
                else {
                    let info = self.tentative_mapping.row_info[row_addr];
                    if idx > 0 && row_addr == prev_addr {
                        ListRowRecoveryInfo::<L>{ head: new_head, next: new_row_addr, ..info }
                    }
                    else if info.head == list_addr {
                        ListRowRecoveryInfo::<L>{ head: new_head, ..info }
                    }
                    else {
                        info
                    }
                }
            }
        );

        let new_tentative_mapping = ListRecoveryMapping::<L>{
            row_info: new_row_info,
            list_info: self.tentative_mapping.list_info.remove(list_addr).insert(new_head, new_addrs),
            list_elements: self.tentative_mapping.list_elements.remove(list_addr).insert(new_head, new_elements),
        };

        let new_allocated_disposition =
            ListRowDisposition::InPendingAllocationList{ pos: self.pending_allocations.len() };
        let new_deallocated_disposition =
            self.row_info[old_row_addr].add_to_pending_deallocations(self.pending_deallocations.len());
        let new_row_dispositions =
            self.row_info.insert(new_row_addr, new_allocated_disposition)
                         .insert(old_row_addr, new_deallocated_disposition);

        let new_modifications = match self.m[list_addr] {
            ListTableEntryView::Durable{ .. } => self.modifications,
            ListTableEntryView::Modified{ which_modification, .. } =>
                self.modifications.update(which_modification as int, Some(new_head)),
        };

        let new_entry = match self.m[list_addr] {
            ListTableEntryView::Durable{ .. } => self.m[list_addr],
            ListTableEntryView::Modified{ which_modification, durable_head, summary, addrs, elements } => {
                let new_summary = ListSummary{
                    head: new_head,
                    tail: new_addrs.last(),
                    length: summary.length,
                    end_of_logical_range: new_elements.last().end(),
                };
                ListTableEntryView::Modified{
                    which_modification,
                    durable_head,
                    summary: new_summary,
                    addrs: addrs.update(idx as int, new_row_addr),
                    elements: elements.update(idx as int, new_element),
                }
            },
        };

        Self{
            free_list: self.free_list.drop_last(),
            tentative_mapping: new_tentative_mapping,
            row_info: new_row_dispositions,
            m: self.m.remove(list_addr).insert(new_head, new_entry),
            pending_allocations: self.pending_allocations.push(new_row_addr),
            pending_deallocations: self.pending_deallocations.push(old_row_addr),
            modifications: new_modifications,
            ..self
        }
    }

    pub(super) proof fn lemma_update_works(
        self,
        list_addr: u64,
        idx: usize,
        new_element: L,
        sm: ListTableStaticMetadata
    )
        requires
            sm.valid::<L>(),
            self.valid(sm),
            0 < sm.start(),
            0 < self.free_list.len(),
            self.m.contains_key(list_addr),
            match self.m[list_addr] {
                ListTableEntryView::Modified{ summary, addrs, elements, .. } => {
                    &&& summary.length == addrs.len()
                    &&& addrs.len() == elements.len()
                    &&& idx < addrs.len()
                    &&& elements[idx as int].start() == new_element.start()
                    &&& elements[idx as int].end() == new_element.end()
                },
                _ => false,
            },
        ensures
            self.update(list_addr, idx, new_element).valid(sm),
            ({
                let new_row_addr = self.free_list.last();
                let new_head = if idx == 0 { new_row_addr } else { list_addr };
                self.update(list_addr, idx, new_element).tentative_mapping.as_snapshot() ==
                    self.tentative_mapping.as_snapshot().update_entry_at_index(list_addr, new_head, idx, new_element)
            }),
    {
        let new_self = self.update(list_addr, idx, new_element);
        let old_snapshot = self.tentative_mapping.as_snapshot();
        let new_snapshot = new_self.tentative_mapping.as_snapshot();

        let new_row_addr = self.free_list.last();
        let new_head = if idx == 0 { new_row_addr } else { list_addr };

        assert(new_snapshot =~= old_snapshot.update_entry_at_index(list_addr, new_head, idx, new_element));
        assert(new_row_addr > 0) by {
            broadcast use group_validate_row_addr;
        }

        match new_self.m[new_head] {
            ListTableEntryView::Modified{ durable_head, summary, addrs, elements, .. } => {
                assert(durable_head == 0);
                assert(summary.length == addrs.len());
                assert(addrs.len() == elements.len());
            },
            _ => { assert(false); },
        }
    }
}

impl<PM, L> ListTable<PM, L>
    where
        PM: PersistentMemoryRegion,
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    exec fn get_addresses_and_elements_case_durable(
        &self,
        list_addr: u64,
        summary: &ListSummary,
        journal: &Journal<TrustedKvPermission, PM>,
        Ghost(prev_self): Ghost<Self>,
    ) -> (result: Result<(Vec<u64>, Vec<L>), KvError>)
        requires
            prev_self.valid(journal@),
            journal.valid(),
            prev_self@.tentative.is_some(),
            prev_self@.tentative.unwrap().m.contains_key(list_addr),
            prev_self.m@.contains_key(list_addr),
            prev_self.m@[list_addr] is Durable,
            summary == prev_self.m@[list_addr]->Durable_summary,
            self == (Self{ m: self.m, ..prev_self }),
            self.m@ == prev_self.m@.remove(list_addr),
        ensures
            match result {
                Ok((addrs, elements)) => {
                    &&& addrs@ == self.tentative_mapping@.list_info[list_addr]
                    &&& elements@ == self.tentative_mapping@.list_elements[list_addr]
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result_addrs = Vec::<u64>::new();
        let mut result_elements = Vec::<L>::new();
        let ghost current_pos: int = 0;
        let ghost addrs = prev_self.durable_mapping@.list_info[list_addr];
        let ghost elements = prev_self.durable_mapping@.list_elements[list_addr];
        let pm = journal.get_pm_region_ref();

        assert(addrs.take(current_pos) =~= Seq::<u64>::empty());
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
                result_addrs@ == addrs.take(current_pos),
                result_elements@ == elements.take(current_pos),
                prev_self.valid(journal@),
                journal.valid(),
                prev_self.durable_mapping@.list_info.contains_key(list_addr),
                addrs == prev_self.durable_mapping@.list_info[list_addr],
                elements == prev_self.durable_mapping@.list_elements[list_addr],
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
                self == (Self{ m: self.m, ..prev_self }),
            decreases
                addrs.len() - result_addrs@.len(),
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(addrs.take(current_pos).push(addrs[current_pos as int]) =~= addrs.take(current_pos + 1));
            assert(elements.take(current_pos).push(elements[current_pos as int]) =~= elements.take(current_pos + 1));

            let element_addr = current_addr + self.sm.row_element_start;
            let element_crc_addr = current_addr + self.sm.row_element_crc_start;
            let current_element = match exec_recover_object::<PM, L>(pm, element_addr, element_crc_addr) {
                Some(e) => e,
                None => { return Err(KvError::CRCMismatch); },
            };

            result_addrs.push(current_addr);
            result_elements.push(current_element);

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
        assert(elements.take(current_pos) =~= elements);
        assert(prev_self.tentative_mapping@.list_info[list_addr] == prev_self.durable_mapping@.list_info[list_addr]);
        assert(prev_self.tentative_mapping@.list_elements[list_addr] ==
               prev_self.durable_mapping@.list_elements[list_addr]);
        Ok((result_addrs, result_elements))
    }

    exec fn get_addresses_and_elements_case_modified(
        &self,
        list_addr: u64,
        summary: &ListSummary,
        journal: &Journal<TrustedKvPermission, PM>,
        num_addrs: usize,
        Ghost(prev_self): Ghost<Self>,
    ) -> (result: Result<(Vec<u64>, Vec<L>), KvError>)
        requires
            prev_self.valid(journal@),
            journal.valid(),
            prev_self@.tentative.is_some(),
            prev_self@.tentative.unwrap().m.contains_key(list_addr),
            prev_self.m@.contains_key(list_addr),
            summary.length > num_addrs,
            match prev_self.m@[list_addr] {
                ListTableEntry::Modified{ summary: s, addrs, .. } => {
                    &&& summary == s
                    &&& addrs.len() == num_addrs
                },
                _ => false,
            },
            self == (Self{ m: self.m, ..prev_self }),
            self.m@ == prev_self.m@.remove(list_addr),
        ensures
            match result {
                Ok((addrs, elements)) => {
                    let num_durable_addrs = summary.length - num_addrs;
                    &&& addrs@ == self.tentative_mapping@.list_info[list_addr].take(num_durable_addrs)
                    &&& elements@ == self.tentative_mapping@.list_elements[list_addr].take(num_durable_addrs)
                },
                Err(KvError::CRCMismatch) => !journal@.pm_constants.impervious_to_corruption(),
                _ => false,
            }
    {
        let mut current_addr = list_addr;
        let mut result_addrs = Vec::<u64>::new();
        let mut result_elements = Vec::<L>::new();
        let ghost durable_head = prev_self.m@[list_addr]->Modified_durable_head@;
        let ghost durable_addrs = prev_self.durable_mapping@.list_info[durable_head];
        let ghost durable_elements = prev_self.durable_mapping@.list_elements[durable_head];
        let ghost tentative_addrs = prev_self.tentative_mapping@.list_info[list_addr];
        let ghost tentative_elements = prev_self.tentative_mapping@.list_elements[list_addr];
        let pm = journal.get_pm_region_ref();

        let num_durable_addrs = summary.length - num_addrs;
        assert(tentative_addrs.take(0) =~= Seq::<u64>::empty());
        assert(tentative_elements.take(0) =~= Seq::<L>::empty());
        assert(tentative_addrs.take(num_durable_addrs as int) =~=
               durable_addrs.skip(durable_addrs.len() - num_durable_addrs));
        assert(tentative_elements.take(num_durable_addrs as int) =~=
               durable_elements.skip(durable_elements.len() - num_durable_addrs));

        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        for current_pos in 0..num_durable_addrs
            invariant
                num_durable_addrs == summary.length - num_addrs,
                0 <= num_addrs < summary.length,
                0 <= current_pos <= num_durable_addrs,
                current_pos < num_durable_addrs ==> current_addr == tentative_addrs[current_pos as int],
                result_addrs@ == tentative_addrs.take(current_pos as int),
                result_elements@ == tentative_elements.take(current_pos as int),
                tentative_addrs.len() == summary.length,
                tentative_elements.len() == summary.length,
                prev_self.valid(journal@),
                journal.valid(),
                prev_self.durable_mapping@.list_info.contains_key(durable_head),
                prev_self.tentative_mapping@.list_info.contains_key(list_addr),
                0 < durable_addrs.len(),
                num_durable_addrs <= durable_addrs.len(),
                durable_addrs.len() == durable_elements.len(),
                durable_addrs == prev_self.durable_mapping@.list_info[durable_head],
                durable_elements == prev_self.durable_mapping@.list_elements[durable_head],
                tentative_addrs == prev_self.tentative_mapping@.list_info[list_addr],
                tentative_elements == prev_self.tentative_mapping@.list_elements[list_addr],
                tentative_addrs.take(num_durable_addrs as int) ==
                    durable_addrs.skip(durable_addrs.len() - num_durable_addrs),
                tentative_elements.take(num_durable_addrs as int) ==
                    durable_elements.skip(durable_elements.len() - num_durable_addrs),
                pm.inv(),
                pm@.read_state == journal@.read_state,
                pm.constants() == journal@.pm_constants,
                self == (Self{ m: self.m, ..prev_self }),
        {
            proof {
                broadcast use group_validate_row_addr;
                broadcast use pmcopy_axioms;
            }

            assert(tentative_addrs.take(current_pos as int).push(tentative_addrs[current_pos as int]) =~=
                   tentative_addrs.take(current_pos + 1));
            assert(tentative_elements.take(current_pos as int).push(tentative_elements[current_pos as int]) =~=
                   tentative_elements.take(current_pos + 1));

            let ghost num_skipped_durable = durable_addrs.len() - num_durable_addrs;
            assert(durable_addrs.skip(num_skipped_durable)[current_pos as int] =~=
                   durable_addrs[num_skipped_durable + current_pos]);
            assert(current_addr == durable_addrs[num_skipped_durable + current_pos]);

            let element_addr = current_addr + self.sm.row_element_start;
            let element_crc_addr = current_addr + self.sm.row_element_crc_start;
            let current_element = match exec_recover_object::<PM, L>(pm, element_addr, element_crc_addr) {
                Some(e) => e,
                None => { return Err(KvError::CRCMismatch); },
            };
            assert(durable_elements.skip(num_skipped_durable)[current_pos as int] =~=
                   durable_elements[num_skipped_durable + current_pos]);
            assert(current_element == durable_elements[num_skipped_durable + current_pos]);
            assert(current_element == tentative_elements[current_pos as int]);

            result_addrs.push(current_addr);
            result_elements.push(current_element);

            if current_pos + 1 < num_durable_addrs {
                let next_addr = current_addr + self.sm.row_next_start;
                let next_crc_addr = next_addr + size_of::<u64>() as u64;
                current_addr = match exec_recover_object::<PM, u64>(pm, next_addr, next_crc_addr) {
                    Some(n) => n,
                    None => { return Err(KvError::CRCMismatch); },
                };
                assert(durable_addrs.skip(num_skipped_durable)[current_pos + 1] =~=
                       durable_addrs[num_skipped_durable + current_pos + 1]);
                assert(current_addr == tentative_addrs[current_pos + 1]);
            }
        }
        
        Ok((result_addrs, result_elements))
    }

    exec fn complete_entry(
        &mut self,
        list_addr: u64,
        entry: ListTableEntry<L>,
        journal: &Journal<TrustedKvPermission, PM>,
        Ghost(prev_self): Ghost<Self>,
    ) -> (result: (bool, ListTableEntry<L>))
        requires
            prev_self.valid(journal@),
            journal.valid(),
            old(self) == (Self{
                m: old(self).m,
                ..prev_self
            }),
            prev_self@.tentative is Some,
            prev_self@.tentative.unwrap().m.contains_key(list_addr),
            prev_self.m@.contains_key(list_addr),
            entry == prev_self.m@[list_addr],
            old(self).m@ == prev_self.m@.remove(list_addr),
        ensures
            journal.valid(),
            self == (Self{ m: self.m, deletes: self.deletes, deletes_inverse: self.deletes_inverse,
                           modifications: self.modifications, ..*old(self) }),
            ({
                let (success, new_entry) = result;
                if success {
                    let next_iv = self.internal_view().add_entry(list_addr, new_entry@);
                    &&& self@ == old(self)@
                    &&& !self.m@.contains_key(list_addr)
                    &&& next_iv.corresponds_to_journal(journal@, self.sm)
                    &&& match new_entry {
                        ListTableEntry::Modified{ summary, addrs, elements, .. } => {
                            &&& summary.length == addrs.len()
                            &&& addrs.len() == elements.len()
                            &&& addrs@ == self.tentative_mapping@.list_info[list_addr]
                            &&& elements@ == self.tentative_mapping@.list_elements[list_addr]
                        },
                        _ => false,
                    }
                }
                else {
                    &&& !journal@.pm_constants.impervious_to_corruption()
                    &&& self == old(self)
                    &&& new_entry == entry
                }
            }),
    {
        let already_complete = match &entry {
            ListTableEntry::Durable{ .. } => false,
            ListTableEntry::Modified{ ref summary, ref addrs, .. } => addrs.len() == summary.length,
        };
        if already_complete {
            proof {
                let next_iv = self.internal_view().add_entry(list_addr, entry@);
                assert(next_iv =~= prev_self.internal_view().complete_entry(list_addr));
                prev_self.internal_view().lemma_complete_entry_maintains_correspondence(
                    list_addr, journal@, self.sm
                );
            }
            return (true, entry);
        }

        match entry {
            ListTableEntry::Durable{ summary } => {
                match self.get_addresses_and_elements_case_durable(list_addr, &summary, journal, Ghost(prev_self)) {
                    Ok((addrs, elements)) => {
                        let which_modification = self.modifications.len();
                        assert(addrs@.skip(0) == addrs@);
                        assert(elements@.skip(0) == elements@);
                        let new_entry = ListTableEntry::Modified{ which_modification, durable_head: Ghost(0),
                                                                  summary, addrs, elements };
                        let ghost which_delete = self.deletes@.len() as nat;
                        self.deletes.push(summary);
                        self.deletes_inverse = Ghost(self.deletes_inverse@.insert(list_addr, which_delete));
                        self.modifications.push(Some(list_addr));
                        proof {
                            let next_iv = self.internal_view().add_entry(list_addr, new_entry@);
                            assert(next_iv =~= prev_self.internal_view().complete_entry(list_addr));
                            prev_self.internal_view().lemma_complete_entry_maintains_correspondence(
                                list_addr, journal@, self.sm
                            );
                        }
                        (true, new_entry)
                    },
                    Err(KvError::CRCMismatch) => {
                        (false, entry)
                    },
                    Err(e) => {
                        assert(false);
                        (false, entry)
                    }
                }
            },

            ListTableEntry::Modified{ which_modification, durable_head, summary, mut addrs, mut elements } => {
                let num_addrs = addrs.len();
                assert(num_addrs < summary.length);
                match self.get_addresses_and_elements_case_modified(list_addr, &summary, journal, num_addrs,
                                                                    Ghost(prev_self)) {
                    Ok((mut durable_addrs, mut durable_elements)) => {
                        durable_addrs.append(&mut addrs);
                        durable_elements.append(&mut elements);
                        let new_entry = ListTableEntry::Modified{
                            which_modification,
                            durable_head: Ghost(0),
                            summary,
                            addrs: durable_addrs,
                            elements: durable_elements,
                        };
                        proof {
                            let next_iv = self.internal_view().add_entry(list_addr, new_entry@);
                            let g_durable_addrs = self.durable_mapping@.list_info[durable_head@];
                            let g_durable_elements = self.durable_mapping@.list_elements[durable_head@];
                            let num_durable_addrs = summary.length - num_addrs;
                            assert(self.tentative_mapping@.list_info[list_addr].take(num_durable_addrs) ==
                                   g_durable_addrs.skip(g_durable_addrs.len() - (summary.length - num_addrs)));
                            assert(durable_addrs@ ==
                                   prev_self.internal_view().tentative_mapping.list_info[list_addr]);
                            assert(self.tentative_mapping@.list_elements[list_addr].take(num_durable_addrs) ==
                                   g_durable_elements.skip(g_durable_elements.len() -
                                                           (summary.length - num_addrs)));
                            assert(durable_elements@ ==
                                   prev_self.internal_view().tentative_mapping.list_elements[list_addr]);
                            assert(next_iv =~= prev_self.internal_view().complete_entry(list_addr));
                            prev_self.internal_view().lemma_complete_entry_maintains_correspondence(
                                list_addr, journal@, self.sm
                            );
                        }
                        (true, new_entry)
                    },
                    Err(KvError::CRCMismatch) => {
                        (false,
                         ListTableEntry::Modified{ which_modification, durable_head, summary, addrs, elements })
                    },
                    Err(e) => {
                        assert(false);
                        (false,
                         ListTableEntry::Modified{ which_modification, durable_head, summary, addrs, elements })
                    }
                }
            },
        }
    }

    exec fn update_normal_case_write_step(
        &self,
        list_addr: u64,
        idx: usize,
        new_element: L,
        entry: &ListTableEntry<L>,
        new_row_addr: u64,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    )
        requires
            self.inv(old(journal)@),
            self.status@ is PoppedEntry,
            Self::recover(old(journal)@.durable_state, self.durable_mapping@.list_elements.dom(), self@.sm)
                == Some(self@.durable),
            self.internal_view()
                .add_entry(list_addr, entry@)
                .push_to_free_list(new_row_addr)
                .corresponds_to_journal(old(journal)@, self.sm),
            old(journal).valid(),
            forall|s: Seq<u8>| self.state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
            idx == 0 || old(journal)@.remaining_capacity >= self.space_needed_to_journal_next,
            match entry {
                ListTableEntry::Modified{ summary, addrs, elements, .. } => {
                    &&& summary.length == addrs.len()
                    &&& addrs.len() == elements.len()
                    &&& idx < addrs.len()
                    &&& elements[idx as int].start() == new_element.start()
                    &&& elements[idx as int].end() == new_element.end()
                },
                _ => false,
            },
        ensures
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            ({
                let old_iv = self.internal_view().add_entry(list_addr, entry@).push_to_free_list(new_row_addr);
                &&& old_iv.corresponds_to_durable_state(journal@.durable_state, self.sm)
                &&& old_iv.corresponds_to_durable_state(journal@.read_state, self.sm)
            }),
            ({
                let addrs = entry->Modified_addrs@;
                let next: u64 = if idx == addrs.len() - 1 { 0 } else { addrs[idx + 1] };
                &&& recover_object::<L>(journal@.commit_state, new_row_addr + self.sm.row_element_start,
                                       new_row_addr + self.sm.row_element_crc_start) == Some(new_element)
                &&& recover_object::<u64>(journal@.commit_state, new_row_addr + self.sm.row_next_start,
                                         new_row_addr + self.sm.row_next_start + u64::spec_size_of()) == Some(next)
                &&& forall|other_row_addr: u64| {
                    &&& self.sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                } ==> {
                    recover_object::<L>(journal@.commit_state, other_row_addr + self.sm.row_element_start,
                                        other_row_addr + self.sm.row_element_crc_start) ==
                    recover_object::<L>(old(journal)@.commit_state, other_row_addr + self.sm.row_element_start,
                                        other_row_addr + self.sm.row_element_crc_start)
                }
            }),
            if idx > 0 {
                let addrs = entry->Modified_addrs@;
                let prev_row_addr: u64 = addrs[idx - 1];
                &&& recover_object::<u64>(journal@.commit_state, prev_row_addr + self.sm.row_next_start,
                                        prev_row_addr + self.sm.row_next_start + u64::spec_size_of()) ==
                        Some(new_row_addr)
                &&& forall|other_row_addr: u64| {
                    &&& self.sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                    &&& other_row_addr != prev_row_addr
                } ==> {
                    recover_object::<u64>(journal@.commit_state, other_row_addr + self.sm.row_next_start,
                                        other_row_addr + self.sm.row_next_start + u64::spec_size_of()) ==
                    recover_object::<u64>(old(journal)@.commit_state, other_row_addr + self.sm.row_next_start,
                                          other_row_addr + self.sm.row_next_start + u64::spec_size_of())
                }
                &&& journal@.journaled_addrs ==
                    old(journal)@.journaled_addrs +
                    Set::<int>::new(|i: int| prev_row_addr + self.sm.row_next_start <= i
                                  < prev_row_addr + self.sm.row_next_start + u64::spec_size_of() + u64::spec_size_of())
            } else {
                &&& forall|other_row_addr: u64| {
                    &&& self.sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                } ==> {
                    recover_object::<u64>(journal@.commit_state, other_row_addr + self.sm.row_next_start,
                                          other_row_addr + self.sm.row_next_start + u64::spec_size_of()) ==
                    recover_object::<u64>(old(journal)@.commit_state, other_row_addr + self.sm.row_next_start,
                                          other_row_addr + self.sm.row_next_start + u64::spec_size_of())
                }
                &&& journal@.journaled_addrs == old(journal)@.journaled_addrs
            },
    {
        let ghost old_iv = self.internal_view().add_entry(list_addr, entry@).push_to_free_list(new_row_addr);
        assert(old_iv.m.contains_key(list_addr)); // Triggers various facts

        proof {
            journal.lemma_valid_implications();
            assert(new_row_addr == old_iv.free_list.last());
            Self::lemma_writing_to_free_slot_has_permission_later_forall(
                old_iv,
                journal@,
                self.sm,
                self.free_list@.len() as int,
                new_row_addr,
                perm
            );

            broadcast use group_validate_row_addr;
            broadcast use pmcopy_axioms;
            broadcast use broadcast_journal_view_matches_in_range_transitive;
        }

        match entry {
            ListTableEntry::Durable{ .. } => { assert(false); },
            ListTableEntry::Modified{ addrs, .. } => {
                assert(old_iv.m[list_addr] == entry@);
                assert(addrs@ == old_iv.tentative_mapping.list_info[list_addr]);
                let element_addr = new_row_addr + self.sm.row_element_start;
                let element_crc_addr = new_row_addr + self.sm.row_element_crc_start;
                let element_crc = calculate_crc(&new_element);
        
                journal.write_object::<L>(element_addr, &new_element, Tracked(perm));
                journal.write_object::<u64>(element_crc_addr, &element_crc, Tracked(perm));
        
                let next_addr = new_row_addr + self.sm.row_next_start;
                let next_crc_addr = next_addr + size_of::<u64>() as u64;
                let next: u64 = if idx == addrs.len() - 1 { 0 } else { addrs[idx + 1] };
                let next_crc = calculate_crc(&next);
        
                journal.write_object::<u64>(next_addr, &next, Tracked(perm));
                journal.write_object::<u64>(next_crc_addr, &next_crc, Tracked(perm));
        
                // Leverage postcondition of `lemma_writing_to_free_slot_has_permission_later_forall`
                // to conclude that `self` is still consistent with both the durable and read state
                // of the journal.
                assert(old_iv.corresponds_to_durable_state(journal@.durable_state, self.sm));
                assert(old_iv.corresponds_to_durable_state(journal@.read_state, self.sm));

                proof {
                    lemma_writing_element_and_next_effect_on_recovery::<L>(
                        old(journal)@.commit_state,
                        journal@.commit_state,
                        new_row_addr,
                        new_element,
                        next,
                        self.sm
                    );
                }

                assert(forall|other_row_addr: u64| {
                    &&& self.sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                } ==> {
                    recover_object::<L>(journal@.commit_state, other_row_addr + self.sm.row_element_start,
                                        other_row_addr + self.sm.row_element_crc_start) ==
                    recover_object::<L>(old(journal)@.commit_state, other_row_addr + self.sm.row_element_start,
                                        other_row_addr + self.sm.row_element_crc_start)
                });

                if idx > 0 {
                    let ghost jv = journal@;
                    
                    let prev_row_addr = addrs[idx - 1];
                    assert(prev_row_addr == old_iv.tentative_mapping.list_info[list_addr][idx - 1]);
                    assert(self.sm.table.validate_row_addr(prev_row_addr));
                    let prev_next_addr = prev_row_addr + self.sm.row_next_start;
                    let prev_next_crc = calculate_crc(&new_row_addr);

                    let mut bytes_to_write = Vec::<u8>::new();
                    extend_vec_u8_from_slice(&mut bytes_to_write, new_row_addr.as_byte_slice());
                    extend_vec_u8_from_slice(&mut bytes_to_write, prev_next_crc.as_byte_slice());

                    match journal.journal_write(prev_next_addr, bytes_to_write) {
                        Ok(()) => {},
                        _ => { assert(false); },
                    }

                    proof {
                        lemma_writing_next_and_crc_together_effect_on_recovery::<L>(
                            jv.commit_state, journal@.commit_state,
                            prev_row_addr, new_row_addr, self.sm
                        );
                    }
                }
            },
        }
    }

    proof fn lemma_update_normal_case(
        old_iv: ListTableInternalView<L>,
        new_iv: ListTableInternalView<L>,
        list_addr: u64,
        idx: usize,
        new_element: L,
        entry: ListTableEntry<L>,
        old_jv: JournalView,
        new_jv: JournalView,
        sm: ListTableStaticMetadata,
        new_row_addr: u64,
        new_list_addr: u64,
    )
        requires
            sm.valid::<L>(),
            0 < sm.start(),
            sm.corresponds_to_journal(old_jv),
            old_jv.valid(),
            old_iv.corresponds_to_journal(old_jv, sm),
            old_iv.tentative_mapping.list_info.contains_key(list_addr),
            idx < old_iv.tentative_mapping.list_info[list_addr].len(),
            new_iv == old_iv.update(list_addr, idx, new_element),
            0 < old_iv.free_list.len(),
            new_row_addr == old_iv.free_list.last(),
            new_list_addr == if idx == 0 { new_row_addr } else { list_addr },
            old_iv.m.contains_key(list_addr),
            match old_iv.m[list_addr] {
                ListTableEntryView::Modified{ summary, addrs, elements, .. } => {
                    &&& summary.length == addrs.len()
                    &&& addrs.len() == elements.len()
                    &&& idx < addrs.len()
                    &&& elements[idx as int].start() == new_element.start()
                    &&& elements[idx as int].end() == new_element.end()
                },
                _ => false,
            },
            ({
                let addrs = old_iv.tentative_mapping.list_info[list_addr];
                let next: u64 = if idx == addrs.len() - 1 { 0 } else { addrs[idx + 1] };
                let prev_row_addr: u64 = if idx == 0 { 0 } else { addrs[idx - 1] };
                &&& recover_object::<L>(new_jv.commit_state, new_row_addr + sm.row_element_start,
                                        new_row_addr + sm.row_element_crc_start) == Some(new_element)
                &&& recover_object::<u64>(new_jv.commit_state, new_row_addr + sm.row_next_start,
                                          new_row_addr + sm.row_next_start + u64::spec_size_of()) == Some(next)
                &&& forall|other_row_addr: u64| {
                    &&& sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                } ==> {
                    recover_object::<L>(new_jv.commit_state, other_row_addr + sm.row_element_start,
                                        other_row_addr + sm.row_element_crc_start) ==
                    recover_object::<L>(old_jv.commit_state, other_row_addr + sm.row_element_start,
                                        other_row_addr + sm.row_element_crc_start)
                }
            }),
            ({
                let elements = old_iv.tentative_mapping.list_elements[list_addr];
                &&& idx < elements.len()
                &&& elements[idx as int].start() == new_element.start()
                &&& elements[idx as int].end() == new_element.end()
            }),
            if idx > 0 {
                let addrs = old_iv.tentative_mapping.list_info[list_addr];
                let prev_row_addr: u64 = addrs[idx - 1];
                &&& recover_object::<u64>(new_jv.commit_state, prev_row_addr + sm.row_next_start,
                                        prev_row_addr + sm.row_next_start + u64::spec_size_of()) ==
                        Some(new_row_addr)
                &&& forall|other_row_addr: u64| {
                    &&& sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                    &&& other_row_addr != prev_row_addr
                } ==> {
                    recover_object::<u64>(new_jv.commit_state, other_row_addr + sm.row_next_start,
                                          other_row_addr + sm.row_next_start + u64::spec_size_of()) ==
                    recover_object::<u64>(old_jv.commit_state, other_row_addr + sm.row_next_start,
                                          other_row_addr + sm.row_next_start + u64::spec_size_of())
                }
                &&& new_jv.journaled_addrs ==
                    old_jv.journaled_addrs +
                    Set::<int>::new(|i: int| prev_row_addr + sm.row_next_start <= i
                                  < prev_row_addr + sm.row_next_start + u64::spec_size_of() + u64::spec_size_of())
            } else {
                &&& forall|other_row_addr: u64| {
                    &&& sm.table.validate_row_addr(other_row_addr)
                    &&& other_row_addr != new_row_addr
                } ==> {
                    recover_object::<u64>(new_jv.commit_state, other_row_addr + sm.row_next_start,
                                        other_row_addr + sm.row_next_start + u64::spec_size_of()) ==
                    recover_object::<u64>(old_jv.commit_state, other_row_addr + sm.row_next_start,
                                        other_row_addr + sm.row_next_start + u64::spec_size_of())
                }
                &&& new_jv.journaled_addrs == old_jv.journaled_addrs
            },
        ensures
            new_iv.valid(sm),
            new_iv.corresponds_to_tentative_state(new_jv.commit_state, sm),
            new_iv.consistent_with_journaled_addrs(new_jv.journaled_addrs, sm),
            new_iv.tentative_mapping.as_snapshot() ==
                old_iv.tentative_mapping.as_snapshot().update_entry_at_index(list_addr, new_list_addr,
                                                                             idx, new_element),
            ({
                let old_list = old_iv.tentative_mapping.as_snapshot().m[list_addr];
                &&& idx < old_list.len()
                &&& old_list[idx as int].start() == new_element.start()
                &&& old_list[idx as int].end() == new_element.end()
            }),
    {
        broadcast use group_validate_row_addr;
        broadcast use broadcast_update_bytes_effect;
        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        broadcast use pmcopy_axioms;
        
        old_iv.lemma_update_works(list_addr, idx, new_element, sm);
    }

    exec fn update_normal_case(
        &mut self,
        list_addr: u64,
        idx: usize,
        new_element: L,
        entry: ListTableEntry<L>,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (new_list_addr: u64)
        requires
            old(self).inv(old(journal)@),
            !old(self).must_abort@,
            old(self).status@ is PoppedEntry,
            old(self).internal_view().add_entry(list_addr, entry@).corresponds_to_journal(old(journal)@, old(self).sm),
            !old(self).m@.contains_key(list_addr),
            old(journal).valid(),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
            idx == 0 || old(journal)@.remaining_capacity >= old(self).space_needed_to_journal_next,
            old(self).free_list.len() > 0,
            list_addr != 0,
            match entry {
                ListTableEntry::Modified{ summary, addrs, elements, .. } => {
                    &&& summary.length == addrs.len()
                    &&& addrs.len() == elements.len()
                    &&& idx < addrs.len()
                    &&& elements[idx as int].start() == new_element.start()
                    &&& elements[idx as int].end() == new_element.end()
                },
                _ => false,
            },
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            new_list_addr != 0,
            new_list_addr == list_addr || new_list_addr == old(self).free_list@.last(),
            self@ == (ListTableView {
                tentative: Some(old(self)@.tentative.unwrap().update_entry_at_index(list_addr, new_list_addr,
                                                                                  idx, new_element)),
                ..old(self)@
            }),
            self.validate_list_addr(new_list_addr),
            ({
                let old_list = old(self)@.tentative.unwrap().m[list_addr];
                &&& idx < old_list.len()
                &&& old_list[idx as int].start() == new_element.start()
                &&& old_list[idx as int].end() == new_element.end()
            }),
    {
        let ghost old_iv = self.internal_view().add_entry(list_addr, entry@);
        let ghost new_iv = old_iv.update(list_addr, idx, new_element);

        proof {
            old_iv.durable_mapping.lemma_corresponds_implies_equals_new(journal@.durable_state,
                                                                        old_iv.durable_mapping.list_elements.dom(),
                                                                        self.sm);
            journal.lemma_valid_implications();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }

        let new_row_addr = match self.free_list.pop() {
            Some(a) => a,
            None => { assert(false); 0 },
        };
        assert(new_row_addr == old_iv.free_list.last());
        assert(new_row_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        self.update_normal_case_write_step(list_addr, idx, new_element, &entry, new_row_addr, journal, Tracked(perm));

        self.tentative_mapping = Ghost(new_iv.tentative_mapping);
        self.row_info = Ghost(new_iv.row_info);
        self.pending_allocations.push(new_row_addr);

        assert(old_iv.m.contains_key(list_addr)); // Triggers various facts

        let new_head = if idx == 0 { new_row_addr } else { list_addr };

        let (which_modification, old_row_addr) = match &entry {
            ListTableEntry::Durable{ .. } => { assert(false); (0usize, 0u64) },
            ListTableEntry::Modified{ ref which_modification, ref addrs, .. } => (*which_modification, addrs[idx]),
        };

        self.pending_deallocations.push(old_row_addr);
        if idx == 0 {
            self.modifications.set(which_modification, Some(new_row_addr));
        }
        else {
            assert(self.modifications[which_modification as int] == Some(list_addr));
        }

        let new_entry = entry.update(idx, new_row_addr, new_element);
        self.m.insert(new_head, new_entry);

        assert(old(self).internal_view().m == old_iv.m.remove(list_addr));
        assert(new_entry@ =~= new_iv.m[new_head]);
        assert(self.internal_view().m == old_iv.m.remove(list_addr).insert(new_head, new_entry@));
        assert(self.internal_view().m =~= new_iv.m);
        assert(self.internal_view() =~= new_iv);

        self.status = Ghost(ListTableStatus::Quiescent);

        proof {
            Self::lemma_update_normal_case(old_iv, new_iv, list_addr, idx, new_element, entry, old(journal)@,
                                           journal@, self.sm, new_row_addr, new_head);
        }

        new_head
    }

    pub exec fn update(
        &mut self,
        list_addr: u64,
        idx: usize,
        new_element: L,
        journal: &mut Journal<TrustedKvPermission, PM>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(old(journal)@),
            old(journal).valid(),
            old(self)@.tentative is Some,
            old(self)@.tentative.unwrap().m.contains_key(list_addr),
            forall|s: Seq<u8>| old(self).state_equivalent_for_me(s, old(journal)@) ==> #[trigger] perm.check_permission(s),
        ensures
            self.valid(journal@),
            journal.valid(),
            journal@.matches_except_in_range(old(journal)@, self@.sm.start() as int, self@.sm.end() as int),
            match result {
                Ok(new_list_addr) => {
                    let old_list = old(self)@.tentative.unwrap().m[list_addr];
                    &&& new_list_addr != 0
                    &&& new_list_addr == list_addr || !old(self)@.tentative.unwrap().m.contains_key(new_list_addr)
                    &&& idx < old_list.len()
                    &&& old_list[idx as int].start() == new_element.start()
                    &&& old_list[idx as int].end() == new_element.end()
                    &&& self@ == (ListTableView {
                        tentative: Some(old(self)@.tentative.unwrap().update_entry_at_index(list_addr, new_list_addr,
                                                                                          idx, new_element)),
                        ..old(self)@
                    })
                    &&& self.validate_list_addr(new_list_addr)
                },
                Err(KvError::IndexOutOfRange{ upper_bound }) => {
                    let old_list = old(self)@.tentative.unwrap().m[list_addr];
                    &&& self@ == old(self)@
                    &&& idx >= old_list.len()
                    &&& upper_bound == old_list.len()
                },
                Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end }) => {
                    let old_list = old(self)@.tentative.unwrap().m[list_addr];
                    &&& self@ == old(self)@
                    &&& idx < old_list.len()
                    &&& old_start == old_list[idx as int].start()
                    &&& old_end == old_list[idx as int].end()
                    &&& new_start == new_element.start()
                    &&& new_end == new_element.end()
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
        proof {
            self.lemma_valid_implications(journal@);
            journal.lemma_valid_implications();
            broadcast use vstd::std_specs::hash::group_hash_axioms;
        }

        if self.free_list.len() == 0 {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        if idx != 0 || journal.remaining_capacity() < self.space_needed_to_journal_next {
            self.must_abort = Ghost(true);
            return Err(KvError::OutOfSpace);
        }

        let entry = match self.m.remove(&list_addr) {
            None => { assert(false); return Err(KvError::InternalError); },
            Some(e) => e,
        };

        let (success, new_entry) = self.complete_entry(list_addr, entry, journal, Ghost(*old(self)));
        if !success {
            self.m.insert(list_addr, new_entry);
            self.must_abort = Ghost(true);
            return Err(KvError::CRCMismatch);
        }

        let result: Result<(), KvError> = match &new_entry {
            ListTableEntry::Durable{ .. } => {
                assert(false);
                Err(KvError::InternalError)
            },

            ListTableEntry::Modified{ ref addrs, ref elements, .. } => {
                if addrs.len() <= idx {
                    Err(KvError::IndexOutOfRange{ upper_bound: addrs.len() })
                }
                else {
                    let current_element = elements[idx];
                    if current_element.start() != new_element.start() || current_element.end() != new_element.end() {
                        Err(KvError::LogicalRangeUpdateNotAllowed{
                            old_start: current_element.start(),
                            old_end: current_element.end(),
                            new_start: new_element.start(),
                            new_end: new_element.end(),
                        })
                    } else {
                        Ok(())
                    }
                }
            },
        };

        match result {
            Ok(()) => {},
            Err(e) => {
                let ghost old_iv = self.internal_view();
                self.m.insert(list_addr, new_entry);
                assert(self.internal_view() =~= old_iv.add_entry(list_addr, new_entry@));
                return Err(e);
            }
        }

        assert(list_addr != 0) by {
            broadcast use group_validate_row_addr;
        }

        self.status = Ghost(ListTableStatus::PoppedEntry);
        Ok(self.update_normal_case(list_addr, idx, new_element, new_entry, journal, Tracked(perm)))
    }
}

}

