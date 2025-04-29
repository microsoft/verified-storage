#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::traits_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::keys::KeyTableRowMetadata;
use super::spec_t::*;

verus! {

impl<PermFactory, PM, K, I, L> UntrustedKvStoreImpl<PermFactory, PM, K, I, L>
where
    PermFactory: PermissionFactory<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + std::fmt::Debug,
    I: PmCopy + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn read_item(
        &self,
        key: &K,
    ) -> (result: Result<I, KvError>)
        requires 
            self.valid(),
        ensures
            match result {
                Ok(item) => {
                    &&& self@.tentative.read_item(*key) matches Ok(i)
                    &&& item == i
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& self@.tentative.read_item(*key) matches Err(e_spec)
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
        Ok(item)
    }

    pub exec fn tentatively_create(
        &mut self,
        key: &K,
        item: &I,
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
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
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
                }
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                },
            }
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => { return Err(KvError::KeyAlreadyExists); },
            None => {},
        };

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update();
        let result = self.items.create::<PermFactory>(item, &mut self.journal, Tracked::<PermFactory>(self.perm_factory.borrow()));
        proof { self.lemma_reflect_item_table_update(self_before_item_create); }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort();
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost self_before_key_create = self.lemma_prepare_for_key_table_update();
        let result = self.keys.create::<PermFactory>(key, item_addr, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_key_table_update(self_before_key_create); }

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
        }

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        assert(self@.tentative =~= old(self)@.tentative.create(*key, *item).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    pub exec fn tentatively_delete(
        &mut self,
        key: &K,
    ) -> (result: Result<(), KvError>)
        requires 
            old(self).valid(),
        ensures 
            self.valid(),
            match result {
                Ok(()) => {
                    &&& self@ == KvStoreView{
                        tentative: self@.tentative,
                        used_transaction_operation_slots: old(self)@.used_transaction_operation_slots + 1,
                        ..old(self)@
                    }
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    &&& old(self)@.used_transaction_operation_slots >= old(self)@.ps.max_operations_per_transaction
                }
                Err(e) => {
                    &&& self@ == old(self)@
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); }
        };

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        self.items.delete(rm.item_addr, &self.journal);

        if rm.list_addr != 0 {
            assert(self.perm_factory == old(self).perm_factory);
            let ghost self_before_list_delete = self.lemma_prepare_for_list_table_update();
            let result = self.lists.delete::<PermFactory>(rm.list_addr, &mut self.journal, Tracked(self.perm_factory.borrow()));
            proof { self.lemma_reflect_list_table_update(self_before_list_delete); }

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
                Err(KvError::CRCMismatch) => {
                    self.status = Ghost(KvStoreStatus::MustAbort);
                    self.internal_abort();
                    return Err(KvError::CRCMismatch);
                },
                _ => { assert(false); return Err(KvError::InternalError); },
            }
        }

        assert(self.journal@.remaining_capacity == old(self).journal@.remaining_capacity);

        let ghost self_before_key_delete = self.lemma_prepare_for_key_table_update();
        let result = self.keys.delete::<PermFactory>(key, key_addr, rm, &mut self.journal, Tracked(self.perm_factory.borrow()));
        proof { self.lemma_reflect_key_table_update(self_before_key_delete); }

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
        }

        self.status = Ghost(KvStoreStatus::Quiescent);

        assert(self@.tentative =~= old(self)@.tentative.delete(*key).unwrap());
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        // It's a little bit tricky to see that the key table's set of
        // list addresses still matches the list table's domain, due
        // to the special treatment of the 0 address. So we need to
        // invoke extensional equality to establish that equivalence.
        assert(self.keys@.tentative.unwrap().list_addrs() =~= self.lists@.tentative.unwrap().m.dom());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }

    // This function performs a tentative update to the item of the specified key 
    // as part of an ongoing transaction.
    pub exec fn tentatively_update_item(
        &mut self,
        key: &K,
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
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                }
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
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Err(e_spec)
                    &&& e_spec == e
                },
            }
    {
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (key_addr, former_rm) = match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => info,
            None => { return Err(KvError::KeyNotFound); },
        };

        self.status = Ghost(KvStoreStatus::ComponentsDontCorrespond);

        assert(self.perm_factory == old(self).perm_factory);
        let ghost self_before_item_create = self.lemma_prepare_for_item_table_update();
        let result = self.items.create::<PermFactory>(new_item, &mut self.journal, Tracked(self.perm_factory.borrow()));
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
        let new_rm = KeyTableRowMetadata{ item_addr, ..former_rm };
        let result = self.keys.update::<PermFactory>(key, key_addr, new_rm, former_rm, &mut self.journal,
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
        }

        self.items.delete(former_rm.item_addr, &self.journal);

        self.status = Ghost(KvStoreStatus::Quiescent);
        self.used_key_slots = Ghost(self.used_key_slots@ + 1);
        self.used_transaction_operation_slots = Ghost(self.used_transaction_operation_slots@ + 1);

        let ghost old_item_addrs = old(self).keys@.tentative.unwrap().item_addrs();
        assert(old_item_addrs.insert(new_rm.item_addr).remove(former_rm.item_addr) =~=
               old_item_addrs.remove(former_rm.item_addr).insert(new_rm.item_addr));
        assert(self@.tentative =~= old(self)@.tentative.update_item(*key, *new_item).unwrap());

        proof {
            self.lemma_using_space_for_transaction_operation_maintains_invariant(*old(self));
        }

        Ok(())
    }
}
    
}
