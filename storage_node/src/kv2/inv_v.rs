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
    pub(super) open spec fn inv_journal_ok(self) -> bool
    {
        &&& self.journal.valid()
        &&& self.journal@.valid()
        &&& self.journal.recover_idempotent()
        &&& self.journal@.constants.app_program_guid == KVSTORE_PROGRAM_GUID
        &&& self.journal@.constants.app_version_number == KVSTORE_PROGRAM_VERSION_NUMBER
        &&& validate_static_metadata::<K, I, L>(self.sm@, self.journal@.constants)
    }

    pub(super) open spec fn inv_static_metadata_matches(self) -> bool
    {
        &&& recover_static_metadata::<K, I, L>(self.journal@.durable_state, self.journal@.constants) == Some(self.sm@)
        &&& states_match_in_static_metadata_area(self.journal@.durable_state, self.journal@.read_state,
                                               self.journal@.constants)
        &&& states_match_in_static_metadata_area(self.journal@.durable_state, self.journal@.commit_state,
                                               self.journal@.constants)
    }

    pub(super) open spec fn inv_tentative_components_exist(self) -> bool
    {
        &&& !(self.status@ is MustAbort) ==> {
            &&& self.keys@.tentative is Some
            &&& self.items@.tentative is Some
            &&& self.lists@.tentative is Some
        }
    }

    pub(super) open spec fn inv_components_valid(self) -> bool
    {
        &&& self.keys@.sm == self.sm@.keys
        &&& self.items@.sm == self.sm@.items
        &&& self.lists@.sm == self.sm@.lists
        &&& self.keys.valid(self.journal@)
        &&& self.items.valid(self.journal@)
        &&& self.lists.valid(self.journal@)
    }

    pub(super) open spec fn inv_components_correspond(self) -> bool
        recommends
            self.inv_tentative_components_exist()
    {
        &&& self.keys@.durable.item_addrs() == self.items@.durable.m.dom()
        &&& self.keys@.durable.list_addrs() == self.lists@.durable.m.dom()
        &&& self.status@ is Quiescent ==> {
            let tentative_keys = self.keys@.tentative.unwrap();
            let tentative_items = self.items@.tentative.unwrap();
            let tentative_lists = self.lists@.tentative.unwrap();
            &&& tentative_keys.item_addrs() == tentative_items.m.dom()
            &&& tentative_keys.list_addrs() == tentative_lists.m.dom()
        }
    }

    pub(super) open spec fn inv_components_finite(self) -> bool
    {
        &&& self.keys@.durable.key_info.dom().finite()
        &&& self.items@.durable.m.dom().finite()
    }

    pub(super) open spec fn inv_used_slots_correspond(self) -> bool
    {
        !(self.status@ is ComponentsDontCorrespond || self.status@ is MustAbort) ==> {
            &&& self.used_key_slots@ >= self.keys@.used_slots
            &&& self.used_key_slots@ >= self.items@.used_slots
            &&& self.used_list_element_slots@ >= self.lists@.used_slots
        }
    }

    pub(super) open spec fn inv(self) -> bool
    {
        &&& self.inv_journal_ok()
        &&& self.sm@.valid::<K, I, L>()
        &&& self.inv_static_metadata_matches()
        &&& self.inv_tentative_components_exist()
        &&& self.inv_components_valid()
        &&& self.inv_components_correspond()
        &&& self.inv_components_finite()
        &&& self.inv_used_slots_correspond()
        &&& decode_policies(self.sm@.encoded_policies) == Some(self.lists@.logical_range_gaps_policy)
    }

    pub(super) proof fn lemma_recover_static_metadata_depends_only_on_my_area(
        &self,
        old_jv: JournalView,
        new_jv: JournalView,
    )
        requires
            old_jv.constants == new_jv.constants,
            validate_static_metadata::<K, I, L>(self.sm@, old_jv.constants),
            recover_static_metadata::<K, I, L>(old_jv.durable_state, old_jv.constants) == Some(self.sm@),
            states_match_in_static_metadata_area(old_jv.durable_state, old_jv.read_state,
                                                 old_jv.constants),
            states_match_in_static_metadata_area(old_jv.durable_state, old_jv.commit_state,
                                                 old_jv.constants),
            old_jv.matches_in_range(
                new_jv,
                old_jv.constants.app_area_start as int,
                old_jv.constants.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()
            ),
        ensures
            recover_static_metadata::<K, I, L>(new_jv.durable_state, new_jv.constants) == Some(self.sm@),
            states_match_in_static_metadata_area(new_jv.durable_state, new_jv.read_state, new_jv.constants),
            states_match_in_static_metadata_area(new_jv.durable_state, new_jv.commit_state, new_jv.constants),
    {
        lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(
            old_jv.durable_state, new_jv.durable_state, self.sm@, old_jv.constants
        );
    }
}

}
