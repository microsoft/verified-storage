#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::*;
use super::impl_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_t::*;

verus! {

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn read_list(&mut self, key: &K) -> (result: Result<&[L], KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@,
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
            return Ok(self.empty_list.as_slice());
        }

        self.lists.read(list_addr, &self.journal)
    }

    pub exec fn read_item_and_list(&mut self, key: &K) -> (result: Result<(I, &[L]), KvError>)
        requires
            old(self).valid(),
        ensures
            self.valid(),
            self@ == old(self)@,
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
            return Ok((item, self.empty_list.as_slice()));
        }

        let lst = match self.lists.read(list_addr, &self.journal) {
            Ok(s) => s,
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            Err(_) => { assert(false); return Err(KvError::KeyNotFound); },
        };
        Ok((item, lst))
    }

    #[inline]
    exec fn tentatively_append_to_list_step1(
        &mut self,
        key: &K,
        key_addr: u64,
        former_rm: &KeyTableRowMetadata,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<u64, KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
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
                    &&& self.lists@ == ListTableView { tentative: self.lists@.tentative, ..old(self).lists@ }
                    &&& self.lists@.tentative is Some
                    &&& self.lists@.tentative.unwrap() == if former_rm.list_addr == 0 {
                        old(self).lists@.tentative.unwrap().create_singleton(list_addr, new_list_entry)
                    } else {
                        old(self).lists@.tentative.unwrap().append(former_rm.list_addr, list_addr, new_list_entry)
                    }
                    &&& match self.lists@.logical_range_gaps_policy {
                        LogicalRangeGapsPolicy::LogicalRangeGapsForbidden =>
                            new_list_entry.start() == end_of_range(old_list),
                        LogicalRangeGapsPolicy::LogicalRangeGapsPermitted =>
                            new_list_entry.start() >= end_of_range(old_list),
                    }
                    &&& self.journal@.matches_except_in_range(old(self).journal@, self.lists@.sm.start() as int,
                                                            self.lists@.sm.end() as int)
                },
                Err(KvError::CRCMismatch) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self.valid()
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self.valid()
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        let ghost self_before_list_append = self.lemma_prepare_for_list_table_update(perm);
        let result =
            if former_rm.list_addr == 0 {
                assert(end_of_range(Seq::<L>::empty()) == 0);
                self.lists.create_singleton(new_list_entry, &mut self.journal, Tracked(perm))
            }
            else {
                self.lists.append(former_rm.list_addr, new_list_entry, &mut self.journal, Tracked(perm))
            };
        proof { self.lemma_reflect_list_table_update(self_before_list_append); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
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
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Err(e_spec)
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

        let list_addr = match self.tentatively_append_to_list_step1(key, key_addr, &former_rm, new_list_entry,
                                                                    Tracked(perm)) {
            Ok(a) => a,
            Err(e) => { return Err(e); },
        };

        if list_addr != former_rm.list_addr {
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort(Tracked(perm));
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);

        assert(self@.tentative =~= old(self)@.tentative.append_to_list(*key, new_list_entry).unwrap());
        Ok(())
    }

    pub exec fn tentatively_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, *new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, *new_item)
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

        let list_addr = match self.tentatively_append_to_list_step1(key, key_addr, &former_rm, new_list_entry,
                                                                    Tracked(perm)) {
            Ok(a) => a,
            Err(e) => { return Err(e); },
        };

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update(perm);
        let result = self.items.create(&new_item, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~=
               old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, *new_item).unwrap());
        Ok(())
    }

    pub exec fn tentatively_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
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

        let ghost self_before_list_update = self.lemma_prepare_for_list_table_update(perm);
        let result = self.lists.update(former_rm.list_addr, idx, new_list_entry, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_list_table_update(self_before_list_update); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
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
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort(Tracked(perm));
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);

        assert(self@.tentative =~=
               old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry).unwrap());
        Ok(())
    }

    pub exec fn tentatively_update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry,
                                                                              *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                },
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry,
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

        let ghost self_before_list_update = self.lemma_prepare_for_list_table_update(perm);
        let result = self.lists.update(former_rm.list_addr, idx, new_list_entry, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_list_table_update(self_before_list_update); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
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

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update(perm);
        let result = self.items.create(&new_item, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                 return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~=
               old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat,
                                                                      new_list_entry, *new_item).unwrap());
        Ok(())
    }

    pub exec fn tentatively_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
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
            assert(self@.tentative.read_item_and_list(*key).unwrap().1.skip(trim_length as int) =~=
                   self@.tentative.read_item_and_list(*key).unwrap().1);
            assert(self@.tentative.trim_list(*key, trim_length as nat).unwrap() =~= self@.tentative);
            return Ok(());
        }

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        let ghost self_before_list_trim = self.lemma_prepare_for_list_table_update(perm);
        let result = self.lists.trim(former_rm.list_addr, trim_length, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_list_table_update(self_before_list_trim); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        if list_addr != former_rm.list_addr {
            let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
            let new_rm = KeyTableRowMetadata{ list_addr, ..former_rm };
            let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
            proof { self.lemma_reflect_key_table_update(self_before_key_update); }

            match result {
                Ok(()) => {},
                Err(KvError::OutOfSpace) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort(Tracked(perm));
                    return Err(KvError::OutOfSpace);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            };
        }

        self.status = Ghost(KvStoreStatus::Quiescent);

        assert(self@.tentative =~= old(self)@.tentative.trim_list(*key, trim_length as nat).unwrap());
        Ok(())
    }

    pub exec fn tentatively_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
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
            return self.tentatively_update_item(key, &new_item, Tracked(perm));
        }

        if former_rm.list_addr == 0 {
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        let ghost self_before_list_trim = self.lemma_prepare_for_list_table_update(perm);
        let result = self.lists.trim(former_rm.list_addr, trim_length, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_list_table_update(self_before_list_trim); }

        let list_addr = match result {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::CRCMismatch);
            },
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            Err(KvError::IndexOutOfRange{ upper_bound }) => {
                self.status = Ghost(KvStoreStatus::Quiescent);
                return Err(KvError::IndexOutOfRange{ upper_bound });
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update(perm);
        let result = self.items.create(&new_item, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_update = self.lemma_prepare_for_key_table_update(perm);
        let new_rm = KeyTableRowMetadata{ item_addr, list_addr };
        let result = self.keys.update(key, key_addr, new_rm, former_rm, &mut self.journal, Tracked(perm));
        proof { self.lemma_reflect_key_table_update(self_before_key_update); }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(new_rm.item_addr != former_rm.item_addr);
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~= old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat,
                                                                                *new_item).unwrap());
        Ok(())
    }
}

}
