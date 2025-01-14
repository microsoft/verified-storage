#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
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
    pub(super) proof fn lemma_establish_recovery_equivalent_for_app(
        &self,
        tracked perm: &TrustedKvPermission,
    )
        requires
            self.valid(),
            forall |s| Self::untrusted_recover(s) == Some(self@.durable) ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(
            s, self.journal@.durable_state) ==> #[trigger] perm.check_permission(s)
    {
        let jc = self.journal@.constants;
        let js = self.journal@.durable_state;
        let sm = self.sm@;
        let keys = self.keys@.durable;

        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::untrusted_recover(s) =~= Some(self@.durable));
        }
    }

    pub(super) proof fn lemma_establish_recovery_equivalent_for_app_after_commit(
        &self,
        tracked perm: &TrustedKvPermission,
    )
        requires
            self.valid(),
            !(self.status@ is MustAbort),
            self.keys@.tentative is Some,
            forall |s| Self::untrusted_recover(s) == Some(self@.tentative) ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(
            s, self.journal@.commit_state) ==> #[trigger] perm.check_permission(s)
    {
        self.journal.lemma_recover_from_commit_idempotent();

        let jc = self.journal@.constants;
        let js = self.journal@.commit_state;
        let sm = self.sm@;
        let keys = self.keys@.tentative.unwrap();

        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js2,
                                                                              self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::untrusted_recover(s) =~= Some(self@.tentative));
        }
    }

    pub(super) proof fn prepare_for_key_table_update(&self, tracked perm: &TrustedKvPermission) -> (result: Self)
        requires
            self.inv_journal_ok(),
            self.inv_static_metadata_matches(),
            self.inv_components_valid(),
            self.inv_tentative_components_exist(),
            forall |s| Self::untrusted_recover(s) == Some(self@.durable) ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
    {
        *self
    }

    pub(super) proof fn reflect_key_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.keys.valid(self.journal@),
            self.journal.valid(),
            self.journal.recover_idempotent(),
            self.journal@.constants_match(old_self.journal@),
            old_self.journal@.matches_except_in_range(self.journal@, self.keys@.sm.start() as int,
                                                      self.keys@.sm.end() as int),
            self == (Self{ keys: self.keys, journal: self.journal, ..old_self }),
            self.keys@ == (KeyTableView{ tentative: self.keys@.tentative, ..old_self.keys@ }),
        ensures
            ({
                let new_self: Self = 
                    if self.keys@.tentative is Some {
                        self
                    } else {
                        Self{ status: Ghost(KvStoreStatus::MustAbort), ..self }
                    };
                new_self.inv()
            })
    {
        broadcast use broadcast_journal_view_matches_in_range_can_narrow_range;
        self.items.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }

    pub(super) proof fn prepare_for_item_table_update(&self, tracked perm: &TrustedKvPermission) -> (result: Self)
        requires
            self.inv_journal_ok(),
            self.inv_static_metadata_matches(),
            self.inv_components_valid(),
            self.inv_tentative_components_exist(),
            forall |s| Self::untrusted_recover(s) == Some(self@.durable) ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
    {
        *self
    }

    pub(super) proof fn reflect_item_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.items.valid(self.journal@),
            self.journal.valid(),
            self.journal.recover_idempotent(),
            self.journal@.constants_match(old_self.journal@),
            old_self.journal@.matches_except_in_range(self.journal@, self.items@.sm.start() as int,
                                                      self.items@.sm.end() as int),
            self == (Self{ items: self.items, journal: self.journal, ..old_self }),
            self.items@ == (ItemTableView{ tentative: self.items@.tentative, ..old_self.items@ }),
        ensures
            ({
                let new_self: Self = 
                    if self.items@.tentative is Some {
                        self
                    } else {
                        Self{ status: Ghost(KvStoreStatus::MustAbort), ..self }
                    };
                new_self.inv()
            })
    {
        broadcast use broadcast_journal_view_matches_in_range_can_narrow_range;
        self.keys.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.keys.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }

    pub(super) proof fn prepare_for_list_table_update(&self, tracked perm: &TrustedKvPermission) -> (result: Self)
        requires
            self.inv_journal_ok(),
            self.inv_static_metadata_matches(),
            self.inv_components_valid(),
            self.inv_tentative_components_exist(),
            forall |s| Self::untrusted_recover(s) == Some(self@.durable) ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
    {
        *self
    }

    pub(super) proof fn reflect_list_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.lists.valid(self.journal@),
            self.journal.valid(),
            self.journal.recover_idempotent(),
            self.journal@.constants_match(old_self.journal@),
            old_self.journal@.matches_except_in_range(self.journal@, self.lists@.sm.start() as int,
                                                      self.lists@.sm.end() as int),
            self == (Self{ lists: self.lists, journal: self.journal, ..old_self }),
            self.lists@ == (ListTableView{ tentative: self.lists@.tentative, ..old_self.lists@ }),
        ensures
            ({
                let new_self: Self = 
                    if self.lists@.tentative is Some {
                        self
                    } else {
                        Self{ status: Ghost(KvStoreStatus::MustAbort), ..self }
                    };
                new_self.inv()
            })
    {
        broadcast use broadcast_journal_view_matches_in_range_can_narrow_range;
        self.keys.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.keys.lemma_valid_implications(self.journal@);
        self.items.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }
}

}
