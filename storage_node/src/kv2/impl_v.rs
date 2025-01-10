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

pub(super) enum KvStoreStatus
{
    Quiescent,
    MustAbort,
}

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn untrusted_read_item(
        &self,
        key: &K,
    ) -> (result: Result<&I, KvError<K>>)
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
        assume(false);
        Err(KvError::NotImplemented)
    }

    // This function performs a tentative update to the item of the specified key 
    // as part of an ongoing transaction.
    pub exec fn untrusted_update_item(
        &mut self,
        key: &K,
        new_item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                }
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                },
                Err(e) => {
                    &&& old(self)@.tentative.update_item(*key, *new_item) matches Err(e_spec)
                    &&& e_spec == e
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_commit(
        &mut self, 
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> {
                ||| Self::untrusted_recover(s) == Some(old(self)@.durable)
                ||| Self::untrusted_recover(s) == Some(old(self)@.tentative)
            },
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => self@ == old(self)@.commit(),
                Err(_) => false,
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_create(
        &mut self,
        key: &K,
        item: &I,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.create(*key, *item) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            }
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_delete(
        &mut self,
        key: &K,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<(), KvError<K>>)
        requires 
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures 
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.delete(*key) matches Ok(new_self)
                    &&& self@.tentative == new_self
                    &&& self@.durable == old(self)@.durable
                },
                Err(KvError::CRCMismatch) => {
                    &&& self@ == old(self)@.abort()
                    &&& !self@.pm_constants.impervious_to_corruption()
                }, 
                Err(KvError::OutOfSpace) => {
                    &&& self@ == old(self)@.abort()
                    // TODO
                }
                Err(e) => {
                    &&& old(self)@.tentative.delete(*key) matches Err(e_spec)
                    &&& e == e_spec
                    &&& self@ == old(self)@
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_read_item_and_list(&self, key: &K) -> (result: Result<(&I, &Vec<L>), KvError<K>>)
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
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_read_list(&self, key: &K) -> (result: Result<&Vec<L>, KvError<K>>)
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
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_read_list_entry_at_index(&self, key: &K, idx: u64) -> (result: Result<&L, KvError<K>>)
        requires
            self.valid()
        ensures
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
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_append_to_list(
        &mut self,
        key: &K,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.append_to_list(*key, new_list_entry) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_append_to_list_and_update_item(
        &mut self,
        key: &K,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.append_to_list_and_update_item(*key, new_list_entry, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_update_list_entry_at_index(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.update_list_entry_at_index(*key, idx as nat, new_list_entry)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_update_list_entry_at_index_and_item(
        &mut self,
        key: &K,
        idx: usize,
        new_list_entry: L,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.update_list_entry_at_index_and_item(*key, idx as nat, new_list_entry, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_trim_list(
        &mut self,
        key: &K,
        trim_length: usize,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.trim_list(*key, trim_length as nat) matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_trim_list_and_update_item(
        &mut self,
        key: &K,
        trim_length: usize,
        new_item: I,
        Tracked(perm): Tracked<&TrustedKvPermission>
    ) -> (result: Result<(), KvError<K>>)
        requires
            old(self).valid(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(old(self)@.durable),
        ensures
            self.valid(),
            self@.constants_match(old(self)@),
            match result {
                Ok(()) => {
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, new_item)
                        matches Ok(new_self)
                    &&& self@.tentative == new_self
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(e) => {
                    &&& old(self)@.tentative.trim_list_and_update_item(*key, trim_length as nat, new_item)
                        matches Err(e_spec)
                    &&& e == e_spec
                },
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

    pub exec fn untrusted_get_keys(&self) -> (result: Result<Vec<K>, KvError<K>>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(keys) => {
                    &&& keys@.to_set() == self@.tentative.get_keys()
                    &&& keys@.no_duplicates()
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        assume(false);
        Err(KvError::NotImplemented)
    }

}

}
