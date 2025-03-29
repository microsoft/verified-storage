#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;
use super::keys::*;
use super::impl_v::*;
use super::lists::*;
use super::spec_t::*;

verus! {

impl<Perm, PermFactory, PM, K, I, L> UntrustedKvStoreImpl<Perm, PermFactory, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PermFactory: PermissionFactory<Seq<u8>, Perm>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    #[inline]
    pub exec fn read_list(&self, key: &K) -> (result: Result<Vec<L>, KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(lst) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (_key_addr, row_metadata) = match self.keys.read(key, Ghost(self.journal@)) {
            None => { return Err(KvError::KeyNotFound); },
            Some(i) => i,
        };

        let list_addr = row_metadata.list_addr;
        if list_addr == 0 {
            return Ok(Vec::<L>::new());
        }

        self.lists.read(list_addr, &self.journal)
    }

    #[inline]
    pub exec fn read_item_and_list(&self, key: &K) -> (result: Result<(I, Vec<L>), KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok((item, lst)) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Ok((i, l))
                    &&& item == i
                    &&& lst@ == l
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item_and_list(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (_key_addr, row_metadata) = match self.keys.read(key, Ghost(self.journal@)) {
            None => { return Err(KvError::KeyNotFound); },
            Some(i) => i,
        };

        let item = match self.items.read(row_metadata.item_addr, &self.journal) {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            Err(_) => { assert(false); return Err(KvError::KeyNotFound); },
        };

        let list_addr = row_metadata.list_addr;
        if list_addr == 0 {
            return Ok((item, Vec::<L>::new()));
        }

        let lst = match self.lists.read(list_addr, &self.journal) {
            Ok(s) => s,
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            Err(_) => { assert(false); return Err(KvError::KeyNotFound); },
        };
        Ok((item, lst))
    }

    #[inline]
    pub exec fn get_list_length(&self, key: &K) -> (result: Result<usize, KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(num_elements) => {
                    &&& self@.tentative.get_list_length(*key) matches Ok(n)
                    &&& num_elements == n
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.get_list_length(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (_key_addr, row_metadata) = match self.keys.read(key, Ghost(self.journal@)) {
            None => { return Err(KvError::KeyNotFound); },
            Some(i) => i,
        };

        let list_addr = row_metadata.list_addr;
        if list_addr == 0 {
            return Ok(0);
        }

        self.lists.get_list_length(list_addr, &self.journal)
    }

    #[inline]
    exec fn tentatively_append_to_list_step1(
        &mut self,
        key: &K,
        key_addr: u64,
        former_rm: &KeyTableRowMetadata,
        new_list_element: L,
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(),
            old(self).keys@.tentative is Some,
            old(self).keys@.tentative.unwrap().key_info.contains_key(*key),
            old(self).keys@.tentative.unwrap().key_info[*key] == *former_rm,
        ensures
            match result {
                Ok(list_addr) => {
                    let old_list = if former_rm.list_addr == 0 { Seq::<L>::empty() }
                                   else { old(self).lists@.tentative.unwrap().m[former_rm.list_addr] };
                    &&& self == Self{ status: Ghost(KvStoreStatus::ComponentsDontCorrespond),
                                     journal: self.journal, lists: self.lists, ..*old(self) }
                    &&& self.inv()
                    &&& list_addr != 0
                    &&& list_addr == former_rm.list_addr || !old(self).lists@.tentative.unwrap().m.contains_key(list_addr)
                    &&& self.lists.validate_list_addr(list_addr)
                    &&& self.lists@ == ListTableView {
                        tentative: self.lists@.tentative,
                        used_slots: self.lists@.used_slots,
                        ..old(self).lists@
                    }
                    &&& self.lists@.used_slots <= old(self).lists@.used_slots + 1
                    &&& self.lists@.tentative is Some
                    &&& self.lists@.tentative.unwrap() == if former_rm.list_addr == 0 {
                        old(self).lists@.tentative.unwrap().create_singleton(list_addr, new_list_element)
                    } else {
                        old(self).lists@.tentative.unwrap().append(former_rm.list_addr, list_addr, new_list_element)
                    }
                    &&& old_list.len() < usize::MAX
                    &&& match self.lists@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_list_element.start() == end_of_range(old_list),
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_list_element.start() >= end_of_range(old_list),
                    }
                    &&& self.journal@.matches_except_in_range(old(self).journal@, self.lists@.sm.start() as int,
                                                            self.lists@.sm.end() as int)
                    &&& self.journal@.remaining_capacity >= old(self).journal@.remaining_capacity -
                           Journal::<Perm, PermFactory, PM>::spec_journal_entry_overhead() -
                           u64::spec_size_of() - u64::spec_size_of()
                },
                Err(KvError::CRCMismatch) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self.valid()
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_element) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        let ghost self_before_list_append = self.lemma_prepare_for_list_table_update();
        let result =
            if former_rm.list_addr == 0 {
                assert(end_of_range(Seq::<L>::empty()) == 0);
                self.lists.create_singleton(new_list_element, &mut self.journal, Tracked(self.perm_factory.borrow()))
            }
            else {
                self.lists.append(former_rm.list_addr, new_list_element, &mut self.journal,
                                  Tracked(self.perm_factory.borrow()))
            };
        proof { self.lemma_reflect_list_table_update(self_before_list_append); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::ListLengthWouldExceedUsizeMax) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::ListLengthWouldExceedUsizeMax);
            }
            Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::PageLeavesLogicalRangeGap{ end_of_valid_range });
            },
            Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::PageOutOfLogicalRangeOrder{ end_of_valid_range });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        Ok(list_addr)
    }

    pub exec fn tentatively_append_to_list(
        &mut self,
        key: &K,
        new_list_element: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.append_to_list(*key, new_list_element) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_element) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        let list_addr = match self.tentatively_append_to_list_step1(key, key_addr, &former_rm, new_list_element) {
            Ok(a) => a,
            Err(e) => { return Err(e); },
        };

        if list_addr != former_rm.list_addr {
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                          Tracked(self.perm_factory.borrow()));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort();
                    proof {
                        old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                    }
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_list_element_slots = Ghost(self.used_list_element_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        assert(self@.tentative =~= old(self)@.tentative.append_to_list(*key, new_list_element).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_element: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_element, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_element, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        let list_addr = match self.tentatively_append_to_list_step1(key, key_addr, &former_rm, new_list_element) {
            Ok(a) => a,
            Err(e) => { return Err(e); },
        };

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update();
        let result = self.items.create(&new_item, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                      Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_list_element_slots = Ghost(self.used_list_element_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~=
               old(self)@.tentative.append_to_list_and_update_item(*key, new_list_element, *new_item).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_update_list_element_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.update_list_element_at_index(*key, idx as nat, new_list_element)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_element_at_index(*key, idx as nat, new_list_element)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_list_update = self.lemma_prepare_for_list_table_update();
        let result = self.lists.update(former_rm.list_addr, idx, new_list_element, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_list_table_update(self_before_list_update); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        if list_addr != former_rm.list_addr {
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                          Tracked(self.perm_factory.borrow()));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort();
                    proof {
                        old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                    }
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_list_element_slots = Ghost(self.used_list_element_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        assert(self@.tentative =~=
               old(self)@.tentative.update_list_element_at_index(*key, idx as nat, new_list_element).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_update_list_element_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_element: L,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_list_element_slots: old(self)@.used_list_element_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.update_list_element_at_index_and_item(*key, idx as nat, new_list_element,
                                                                              *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_list_element_slots >= old(self)@.ps.max_list_elements
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_element_at_index_and_item(*key, idx as nat, new_list_element,
                                                                             *new_item) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_list_update = self.lemma_prepare_for_list_table_update();
        let result = self.lists.update(former_rm.list_addr, idx, new_list_element, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_list_table_update(self_before_list_update); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::LogicalRangeUpdateNotAllowed{ old_start, old_end, new_start, new_end });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update();
        let result = self.items.create(&new_item, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                      Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_list_element_slots = Ghost(self.used_list_element_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~=
               old(self)@.tentative.update_list_element_at_index_and_item(*key, idx as nat,
                                                                      new_list_element, *new_item).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        if trim_length == 0 {
            self.used_key_slots = Ghost(self.used_key_slots@ + 1);
            self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);
            assert(self@.tentative.read_item_and_list(*key).unwrap().1.skip(trim_length as int) =~=
                   self@.tentative.read_item_and_list(*key).unwrap().1);
            assert(self@.tentative.trim_list(*key, trim_length as nat).unwrap() =~= self@.tentative);
            proof {
                self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
            }
            assert(self.perm_factory == old(self).perm_factory);
            return Ok(());
        }

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_list_trim = self.lemma_prepare_for_list_table_update();
        let result = self.lists.trim(former_rm.list_addr, trim_length, &mut self.journal,
                                     Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_list_table_update(self_before_list_trim); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        if list_addr != former_rm.list_addr {
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                          Tracked(self.perm_factory.borrow()));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort();
                    proof {
                        old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                    }
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        assert(self@.tentative =~= old(self)@.tentative.trim_list(*key, trim_length as nat).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: &I,
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_key_slots: old(self)@.used_key_slots + 1,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& {
                        ||| old(self)@.used_key_slots >= old(self)@.ps.max_keys
                        ||| old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                    }
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };
        if trim_length == 0 {
            assert(self@.tentative.read_item_and_list(*key).unwrap().1.skip(trim_length as int) =~=
                   self@.tentative.read_item_and_list(*key).unwrap().1);
            assert(self@.tentative.trim_list_and_update_item(*key, trim_length as nat, *new_item) =~=
                   self@.tentative.update_item(*key, *new_item));
            return self.tentatively_update_item(key, &new_item);
        }

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_list_trim = self.lemma_prepare_for_list_table_update();
        let result = self.lists.trim(former_rm.list_addr, trim_length, &mut self.journal,
                                     Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_list_table_update(self_before_list_trim); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update();
        let result = self.items.create(&new_item, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update();
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal,
                                      Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                proof {
                    old(self).lemma_insufficient_space_for_transaction_operation_indicates_all_slots_used();
                }
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(new_rm.item_addr != former_rm.item_addr);
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~= old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat,
                                                                                *new_item).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }
}

}
