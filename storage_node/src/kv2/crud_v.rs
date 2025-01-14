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
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::*;
use super::keys::*;
use super::items::*;
use super::impl_t::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
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
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        let (_key_addr, row_metadata) = match self.keys.read(key, Ghost(self.journal@)) {
            None => { return Err(KvError::<K>::KeyNotFound); },
            Some(i) => i,
        };
        let item_addr = row_metadata.item_addr;
        let item = match self.items.read::<K>(item_addr, Ghost(self.journal@)) {
            Ok(i) => i,
            Err(_) => { assert(false); return Err(KvError::<K>::KeyNotFound); },
        };
        Ok(item)
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
        proof {
            self.keys.lemma_valid_implications(self.journal@);
        }

        match self.keys.read(key, Ghost(self.journal@)) {
            Some(info) => { return Err(KvError::<K>::KeyAlreadyExists); },
            None => {},
        };

        let result = self.items.create::<K>(item, &mut self.journal);
        proof {
            broadcast use broadcast_journal_view_matches_in_range_can_narrow_range;
            self.keys.lemma_valid_depends_only_on_my_area(old(self).journal@, self.journal@);
            self.keys.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_depends_only_on_my_area(old(self).journal@, self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            self.lemma_recover_static_metadata_depends_only_on_my_area(old(self).journal@, self.journal@);
        }

        let item_addr = match result {
            Ok(i) => i,
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let ghost journal_after_item_update = self.journal@;
        let result = self.keys.create(key, item_addr, &mut self.journal);
        proof {
            broadcast use broadcast_journal_view_matches_in_range_can_narrow_range;
            self.items.lemma_valid_depends_only_on_my_area(journal_after_item_update, self.journal@);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_depends_only_on_my_area(journal_after_item_update, self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            self.lemma_recover_static_metadata_depends_only_on_my_area(journal_after_item_update, self.journal@);
        }

        match result {
            Ok(()) => {},
            Err(KvError::OutOfSpace) => {
                self.status = Ghost(KvStoreStatus::MustAbort);
                self.internal_abort(Tracked(perm));
                return Err(KvError::OutOfSpace);
            },
            _ => { assert(false); return Err(KvError::InternalError); },
        }

        assert(self@.tentative =~= old(self)@.tentative.create(*key, *item).unwrap());
        Ok(())
    }
}
    
}
