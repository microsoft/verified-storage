#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use std::hash::Hash;
use super::impl_v::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;

verus! {

impl<PermFactory, PM, K, I, L> UntrustedKvStoreImpl<PermFactory, PM, K, I, L>
where
    PermFactory: PermissionFactory<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub(super) proof fn lemma_establish_recovery_equivalent_for_app(perm_factory: PermFactory)
        requires
            forall|s1: Seq<u8>, s2: Seq<u8>| Self::recover(s1) == Self::recover(s2) ==>
                #[trigger] perm_factory.permits(s1, s2)
        ensures
            forall|s1: Seq<u8>, s2: Seq<u8>|
                Journal::<PM>::recovery_equivalent_for_app(s1, s2)
            ==> #[trigger] perm_factory.permits(s1, s2),
    {
        assert forall|s1: Seq<u8>, s2: Seq<u8>|
                   Journal::<PM>::recovery_equivalent_for_app(s1, s2)
               implies #[trigger] perm_factory.permits(s1, s2) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let r1 = Journal::<PM>::recover(s1).unwrap();
            let jc = r1.constants;
            let js1 = r1.state;
            let r2 = Journal::<PM>::recover(s2).unwrap();
            let js2 = r2.state;
            assert(r1.constants == r2.constants);
            if jc.app_program_guid != KVSTORE_PROGRAM_GUID || jc.app_version_number != KVSTORE_PROGRAM_VERSION_NUMBER {
            }
            else if jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of() > jc.app_area_end {
                assert(Self::recover(s1) is None && Self::recover(s2) is None) by {
                    reveal(recover_static_metadata);
                }
            }
            else {
                assert(states_match_in_static_metadata_area(js1, js2, jc));
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js1, js2, jc);
                match recover_static_metadata::<K, I, L>(js1, jc) {
                    None => {},
                    Some(sm) => {
                        assert(validate_static_metadata::<K, I, L>(sm, jc)) by {
                            reveal(recover_static_metadata);
                        }
                        if {
                               ||| jc.journal_capacity <
                                     sm.max_operations_per_transaction * spec_space_needed_for_transaction_operation()
                               ||| sm.setup_parameters() is None
                               ||| !sm.setup_parameters().unwrap().valid()
                           } {
                        }
                        else {
                            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
                                js1, js2, sm.keys
                            );
                            match KeyTable::<PM, K>::recover(js1, sm.keys) {
                                None => {},
                                Some(keys) => {
                                    ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                                        js1, js2, keys.item_addrs(), sm.items
                                    );
                                    match ItemTable::<PM, I>::recover(js1, keys.item_addrs(),
                                                                                         sm.items) {
                                        None => {},
                                        Some(items) => {
                                            ListTable::<PM, L>::
                                                lemma_recover_depends_only_on_my_area(js1, js2, keys.list_addrs(),
                                                                                      sm.lists);
                                        },
                                    }
                                },
                            }
                        }
                    },
                }
            }
        }
    }

    pub(super) proof fn lemma_recover_to_durable_state(&self)
        requires
            self.valid(),
        ensures
            Self::recover(self.journal@.durable_state) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }),
    {
        let s = self.journal@.durable_state;
        let jc = self.journal@.constants;
        let sm = self.sm@;
        let js = Journal::<PM>::recover(s).unwrap().state;

        lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js, jc);

        self.keys.lemma_valid_implications(self.journal@);
        self.items.lemma_valid_implications(self.journal@);
        self.lists.lemma_valid_implications(self.journal@);

        KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
            self.journal@.durable_state, js, sm.keys
        );
        ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
            self.journal@.durable_state, js, self.items@.durable.m.dom(), sm.items
        );
        ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
            self.journal@.durable_state, js, self.lists@.durable.m.dom(), sm.lists
        );
    }

    pub(super) proof fn lemma_establish_recovery_equivalent_for_app_on_commit<Perm>(self, perm: Perm)
        where
            Perm: CheckPermission<Seq<u8>>,
        requires
            self.valid(),
            forall|s1: Seq<u8>, s2: Seq<u8>| #[trigger] perm.permits(s1, s2) <== ({
                &&& Self::recover(s1) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                &&& Self::recover(s2) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.tentative })
            } || {
                &&& Self::recover(s1) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
                &&& Self::recover(s2) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })
            }),
        ensures
            forall|s1: Seq<u8>, s2: Seq<u8>| ({
                &&& Journal::<PM>::recovery_equivalent_for_app(s1, self.journal@.durable_state)
                &&& Journal::<PM>::recovery_equivalent_for_app(s2, self.journal@.commit_state)
            } || {
                &&& Journal::<PM>::recovery_equivalent_for_app(s1, self.journal@.durable_state)
                &&& Journal::<PM>::recovery_equivalent_for_app(s2, self.journal@.durable_state)
            }) ==> #[trigger] perm.permits(s1, s2),
    {
        self.journal.lemma_recover_from_commit_idempotent();

        let jc = self.journal@.constants;
        let js = self.journal@.commit_state;
        let sm = self.sm@;
        let keys = self.keys@.tentative.unwrap();

        assert forall|s1: Seq<u8>, s2: Seq<u8>| ({
                &&& Journal::<PM>::recovery_equivalent_for_app(s1, self.journal@.durable_state)
                &&& Journal::<PM>::recovery_equivalent_for_app(s2, self.journal@.commit_state)
            } || {
                &&& Journal::<PM>::recovery_equivalent_for_app(s1, self.journal@.durable_state)
                &&& Journal::<PM>::recovery_equivalent_for_app(s2, self.journal@.durable_state)
            }) implies #[trigger] perm.permits(s1, s2) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js1 = Journal::<PM>::recover(s1).unwrap().state;
            let js2 = Journal::<PM>::recover(s2).unwrap().state;

            if Journal::<PM>::recovery_equivalent_for_app(s2, self.journal@.commit_state) {
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js1, jc);
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state,
                                                                                  self.journal@.commit_state, jc);
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.commit_state, js2, jc);
                self.keys.lemma_valid_implications(self.journal@);
                self.items.lemma_valid_implications(self.journal@);
                self.lists.lemma_valid_implications(self.journal@);
                KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, sm.keys
                );
                KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
                    self.journal@.commit_state, js2, sm.keys
                );
                ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, self.items@.durable.m.dom(), sm.items
                );
                ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                    self.journal@.commit_state, js2, keys.item_addrs(), sm.items
                );
                ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, self.lists@.durable.m.dom(), sm.lists
                );
                ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                    self.journal@.commit_state, js2, keys.list_addrs(), sm.lists
                );
                assert(Self::recover(s1) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
                assert(Self::recover(s2) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.tentative }));
            } else {
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js1, jc);
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state,
                                                                                  self.journal@.durable_state, jc);
                lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(self.journal@.durable_state, js2, jc);
                self.keys.lemma_valid_implications(self.journal@);
                self.items.lemma_valid_implications(self.journal@);
                self.lists.lemma_valid_implications(self.journal@);
                KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, sm.keys
                );
                KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js2, sm.keys
                );
                ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, self.items@.durable.m.dom(), sm.items
                );
                ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js2, self.items@.durable.m.dom(), sm.items
                );
                ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js1, self.lists@.durable.m.dom(), sm.lists
                );
                ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                    self.journal@.durable_state, js2, self.lists@.durable.m.dom(), sm.lists
                );
                assert(Self::recover(s1) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
                assert(Self::recover(s2) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
            }
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

    pub(super) proof fn lemma_prepare_for_key_table_update(&self) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
        ensures
            result == self,
            self.keys.perm_factory_permits_states_equivalent_for_me(self.journal@, self.perm_factory@),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(KeyTable::<PM, K>::recover(js, sm.keys) == Some(self.keys@.durable)) by {
            self.keys.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s1: Seq<u8>, s2: Seq<u8>| {
            &&& KeyTable::<PM, K>::state_equivalent_for_me(s1, js, jc, self.keys@.sm)
            &&& KeyTable::<PM, K>::state_equivalent_for_me(s2, js, jc, self.keys@.sm)
        } implies #[trigger] self.perm_factory@.permits(s1, s2) by {
            let js1 = Journal::<PM>::recover(s1).unwrap().state;
            let js2 = Journal::<PM>::recover(s2).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js1, jc);
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, jc);
            self.items.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                js, js1, self.items@.durable.m.dom(), sm.items
            );
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                js, js2, self.items@.durable.m.dom(), sm.items
            );
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                js, js1, self.lists@.durable.m.dom(), sm.lists
            );
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                js, js2, self.lists@.durable.m.dom(), sm.lists
            );
            assert(Self::recover(s1) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
            assert(Self::recover(s2) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
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
            self@.powerpm_id == old_self@.powerpm_id,
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

    pub(super) proof fn lemma_prepare_for_item_table_update(&self) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
        ensures
            result == self,
            self.items.perm_factory_permits_states_equivalent_for_me(self.journal@, self.perm_factory@),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(ItemTable::<PM, I>::recover(js, self.items@.durable.m.dom(), sm.items) ==
               Some(self.items@.durable)) by
        {
            self.items.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s1: Seq<u8>, s2: Seq<u8>| {
            &&& ItemTable::<PM, I>::state_equivalent_for_me(
                   s1, js, self.items@.durable.m.dom(), jc, self.items@.sm
               )
            &&& ItemTable::<PM, I>::state_equivalent_for_me(
                   s2, js, self.items@.durable.m.dom(), jc, self.items@.sm
               )
        } implies #[trigger] self.perm_factory@.permits(s1, s2) by {
            let js1 = Journal::<PM>::recover(s1).unwrap().state;
            let js2 = Journal::<PM>::recover(s2).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js1, jc);
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js1, sm.keys);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                js, js1, self.lists@.durable.m.dom(), sm.lists
            );
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(
                js, js2, self.lists@.durable.m.dom(), sm.lists
            );
            assert(Self::recover(s1) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
            assert(Self::recover(s2) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
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
            self@.powerpm_id == old_self@.powerpm_id,
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

    pub(super) proof fn lemma_prepare_for_list_table_update(&self) -> (result: Self)
        requires
            self.inv(),
            self.status@ is ComponentsDontCorrespond,
        ensures
            result == self,
            self.lists.perm_factory_permits_states_equivalent_for_me(self.journal@, self.perm_factory@),
    {
        let ghost jc = self.journal@.constants;
        let ghost js = self.journal@.durable_state;
        let ghost sm = self.sm@;

        assert(ListTable::<PM, L>::recover(js, self.lists@.durable.m.dom(), sm.lists) ==
               Some(self.lists@.durable)) by
        {
            self.lists.lemma_valid_implications(self.journal@);
        }
        assert(Self::recover(js) == Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable })) by {
            self.lemma_inv_implies_recover_works();
        }

        broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        assert forall|s1: Seq<u8>, s2: Seq<u8>| {
            &&& ListTable::<PM, L>::state_equivalent_for_me(
                s1, self.journal@.durable_state, self.lists@.durable.m.dom(), self.journal@.constants, self.lists@.sm
            )
            &&& ListTable::<PM, L>::state_equivalent_for_me(
                s2, self.journal@.durable_state, self.lists@.durable.m.dom(), self.journal@.constants, self.lists@.sm
            )
        } implies #[trigger] self.perm_factory@.permits(s1, s2) by {
            let js1 = Journal::<PM>::recover(s1).unwrap().state;
            let js2 = Journal::<PM>::recover(s2).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js1, jc);
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, jc);
            self.keys.lemma_valid_implications(self.journal@);
            self.lists.lemma_valid_implications(self.journal@);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js1, sm.keys);
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                js, js1, self.items@.durable.m.dom(), sm.items
            );
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(
                js, js2, self.items@.durable.m.dom(), sm.items
            );
            assert(Self::recover(s1) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
            assert(Self::recover(s2) =~= Some(RecoveredKvStore::<K, I, L>{ ps: self@.ps, kv: self@.durable }));
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
            self@.powerpm_id == old_self@.powerpm_id,
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
