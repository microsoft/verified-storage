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
    pub exec fn untrusted_read_list(&mut self, key: &K) -> (result: Result<&[L], KvError>)
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

    pub exec fn untrusted_read_item_and_list(&mut self, key: &K) -> (result: Result<(I, &[L]), KvError>)
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

    pub exec fn untrusted_read_list_entry_at_index(&mut self, key: &K, idx: usize) -> (result: Result<&L, KvError>)
        requires
            old(self).valid()
        ensures
            self.valid(),
            self@ == old(self)@,
            match result {
                Ok(list_entry) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Ok((e))
                    &&& *list_entry == e
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_list_entry_at_index(*key, idx as nat) matches Err(e_spec)
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
            return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
        }

        self.lists.read_entry_at_index(list_addr, idx, &self.journal)
    }

    pub exec fn untrusted_append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
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
                    // TODO
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

    pub exec fn untrusted_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                },
                Err(e) => {
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
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
               old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item).unwrap());
        Ok(())
    }

    pub exec fn untrusted_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
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
                    // TODO
                },
                Err(e) => {
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

    pub exec fn untrusted_update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{ tentative: self@.tentative, ..old(self)@ }
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                },
                Err(e) => {
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
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
                                                                      new_list_entry, new_item).unwrap());
        Ok(())
    }

    pub exec fn untrusted_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
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
                    // TODO
                },
                Err(e) => {
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

        if former_rm.list_addr == 0 {
            if trim_length == 0 {
                assert(old(self)@.tentative.trim_list(*key, trim_length as nat) =~= Ok(old(self)@.tentative)) by {
                    let v1 = old(self)@.tentative;
                    let v2 = v1.trim_list(*key, trim_length as nat).unwrap();
                    assert(v2[*key] =~= v1[*key]);
                    assert(v2 =~= v1);
                }
                return Ok(());
            }
            else {
                return Err(KvError::IndexOutOfRange{ upper_bound: 0 });
            }
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
}

}
