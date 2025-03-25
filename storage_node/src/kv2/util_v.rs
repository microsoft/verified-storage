#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;
use super::{KvStoreStatus, UntrustedKvStoreImpl};
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

impl<Perm, PM, K, I, L> UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub(super) proof fn lemma_establish_recovery_equivalent_for_app(
        &self,
        tracked perm: &Perm,
    )
        requires
            self.valid(),
            forall |s| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<Perm, PM>::recovery_equivalent_for_app(
            s, self.journal@.durable_state) ==> #[trigger] perm.check_permission(s)
    {
        let jc = self.journal@.constants;
        let js = self.journal@.durable_state;
        let sm = self.sm@;
        let keys = self.keys@.durable;

        assert forall|s: Seq<u8>| Journal::<Perm, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<Perm, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<Perm, PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<Perm, PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<Perm, PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::recover(s) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
        }
    }

    pub(super) proof fn lemma_establish_recovery_equivalent_for_app_after_commit(
        &self,
        tracked perm: &Perm,
    )
        requires
            self.valid(),
            !(self.status@ is MustAbort),
            self.keys@.tentative is Some,
            forall |s| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.tentative })
                ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<Perm, PM>::recovery_equivalent_for_app(
            s, self.journal@.commit_state) ==> #[trigger] perm.check_permission(s)
    {
        self.journal.lemma_recover_from_commit_idempotent();

        let jc = self.journal@.constants;
        let js = self.journal@.commit_state;
        let sm = self.sm@;
        let keys = self.keys@.tentative.unwrap();

        assert forall|s: Seq<u8>| Journal::<Perm, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<Perm, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js2,
                                                                              self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<Perm, PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<Perm, PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<Perm, PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::recover(s) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.tentative }));
        }
    }

    pub(super) proof fn lemma_inv_implies_recover_works(&self)
        requires
            self.inv(),
        ensures
            Self::recover(self.journal@.durable_state) ==
                Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }),
    {
        self.keys.lemma_valid_implications(self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        assert(Self::recover(self.journal@.durable_state) =~=
               Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
    }

    pub(super) proof fn lemma_prepare_for_key_table_update(&self, tracked perm: &Perm) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
            forall |s| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
            forall|s: Seq<u8>| self.keys.state_equivalent_for_me(s, self.journal@) ==> #[trigger] perm.check_permission(s),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(KeyTable::<Perm, PM, K>::recover(js, sm.keys) == Some(self.keys@.durable)) by {
            self.keys.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s: Seq<u8>| self.keys.state_equivalent_for_me(s, self.journal@)
                   implies #[trigger] perm.check_permission(s) by {
            let js2 = Journal::<Perm, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            ItemTable::<Perm, PM, I>::lemma_recover_depends_only_on_my_area(js, js2, self.items@.durable.m.dom(), sm.items);
            ListTable::<Perm, PM, L>::lemma_recover_depends_only_on_my_area(js, js2, self.lists@.durable.m.dom(), sm.lists);
            assert(Self::recover(s) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
        }

        *self
    }

    pub(super) proof fn lemma_reflect_key_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.keys.valid(self.journal@),
            self.journal.valid(),
            old_self.journal@.matches_except_in_range(self.journal@, self.keys@.sm.start() as int,
                                                      self.keys@.sm.end() as int),
            self == (Self{ keys: self.keys, journal: self.journal, ..old_self }),
            self.keys@ == (KeyTableView{
                tentative: self.keys@.tentative,
                used_slots: self.keys@.used_slots,
                ..old_self.keys@
            }),
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
        self.journal.lemma_valid_implications();
        self.items.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }

    pub(super) proof fn lemma_prepare_for_item_table_update(&self, tracked perm: &Perm) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
            forall |s| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
            forall|s: Seq<u8>| self.items.state_equivalent_for_me(s, self.journal@) ==> #[trigger] perm.check_permission(s),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(ItemTable::<Perm, PM, I>::recover(js, self.items@.durable.m.dom(), sm.items) == Some(self.items@.durable)) by
        {
            self.items.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s: Seq<u8>| self.items.state_equivalent_for_me(s, self.journal@)
                   implies #[trigger] perm.check_permission(s) by {
            let js2 = Journal::<Perm, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<Perm, PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ListTable::<Perm, PM, L>::lemma_recover_depends_only_on_my_area(js, js2, self.lists@.durable.m.dom(), sm.lists);
            assert(Self::recover(s) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
        }

        *self
    }

    pub(super) proof fn lemma_reflect_item_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.items.valid(self.journal@),
            self.journal.valid(),
            old_self.journal@.matches_except_in_range(self.journal@, self.items@.sm.start() as int,
                                                      self.items@.sm.end() as int),
            self == (Self{ items: self.items, journal: self.journal, ..old_self }),
            self.items@ == (ItemTableView{
                tentative: self.items@.tentative,
                used_slots: self.items@.used_slots,
                ..old_self.items@
            }),
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
        self.journal.lemma_valid_implications();
        self.keys.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.keys.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }

    pub(super) proof fn lemma_prepare_for_list_table_update(&self, tracked perm: &Perm) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
            forall |s| Self::recover(s) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                ==> #[trigger] perm.check_permission(s),
        ensures
            result == self,
            forall|s: Seq<u8>| self.lists.state_equivalent_for_me(s, self.journal@) ==> #[trigger] perm.check_permission(s),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(ListTable::<Perm, PM, L>::recover(js, self.lists@.durable.m.dom(), sm.lists) == Some(self.lists@.durable)) by
        {
            self.lists.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s: Seq<u8>| self.lists.state_equivalent_for_me(s, self.journal@)
                   implies #[trigger] perm.check_permission(s) by {
            let js2 = Journal::<Perm, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<Perm, PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<Perm, PM, I>::lemma_recover_depends_only_on_my_area(js, js2, self.items@.durable.m.dom(),
                                                                            sm.items);
            assert(Self::recover(s) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
        }

        *self
    }

    pub(super) proof fn lemma_reflect_list_table_update(self, old_self: Self)
        requires
            old_self.inv(),
            old_self.status@ is ComponentsDontCorrespond,
            self.lists.valid(self.journal@),
            self.journal.valid(),
            old_self.journal@.matches_except_in_range(self.journal@, self.lists@.sm.start() as int,
                                                      self.lists@.sm.end() as int),
            self == (Self{ lists: self.lists, journal: self.journal, ..old_self }),
            self.lists@ == (ListTableView{
                tentative: self.lists@.tentative,
                used_slots: self.lists@.used_slots,
                ..old_self.lists@
            }),
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
        self.journal.lemma_valid_implications();
        self.keys.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.keys.lemma_valid_implications(self.journal@);
        self.items.lemma_valid_depends_only_on_my_area(old_self.journal@, self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_implications(self.journal@);
        self.lemma_recover_static_metadata_depends_only_on_my_area(old_self.journal@, self.journal@);
    }
}

}
