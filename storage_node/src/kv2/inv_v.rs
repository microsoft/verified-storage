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
    pub(super) open spec fn inv(self) -> bool
    {
        &&& self.journal.valid()
        &&& self.journal@.valid()
        &&& self.journal.recover_idempotent()
        &&& self.journal@.constants.app_program_guid == KVSTORE_PROGRAM_GUID
        &&& self.journal@.constants.app_version_number == KVSTORE_PROGRAM_VERSION_NUMBER
        &&& self.id == self.sm@.id
        &&& self.sm@.valid::<K, I, L>()
        &&& recover_static_metadata::<K, I, L>(self.journal@.durable_state, self.journal@.constants) == Some(self.sm@)
        &&& states_match_in_static_metadata_area(self.journal@.durable_state, self.journal@.read_state,
                                               self.journal@.constants)
        &&& states_match_in_static_metadata_area(self.journal@.durable_state, self.journal@.commit_state,
                                               self.journal@.constants)
        &&& validate_static_metadata::<K, I, L>(self.sm@, self.journal@.constants)
        &&& self.keys@.sm == self.sm@.keys
        &&& self.keys.valid(self.journal@)
        &&& self.items@.sm == self.sm@.items
        &&& self.items.valid(self.journal@)
        &&& self.lists@.sm == self.sm@.lists
        &&& self.lists.valid(self.journal@)
        &&& self.keys@.durable.item_addrs() == self.items@.durable.m.dom()
        &&& self.keys@.durable.list_addrs() == self.lists@.durable.m.dom()
        &&& decode_policies(self.sm@.encoded_policies) == Some(self.lists@.logical_range_gaps_policy)
        &&& self.lists@.durable.m.contains_key(0)
        &&& self.lists@.durable.m[0] == Seq::<L>::empty()
        &&& !(self.status@ is MustAbort) ==> {
            &&& self.keys@.tentative matches Some(tentative_keys)
            &&& self.items@.tentative matches Some(tentative_items)
            &&& self.lists@.tentative matches Some(tentative_lists)
            &&& tentative_keys.item_addrs() == tentative_items.m.dom()
            &&& tentative_keys.list_addrs() == tentative_lists.m.dom()
            &&& tentative_lists.m.contains_key(0)
            &&& tentative_lists.m[0] == Seq::<L>::empty()
        }
    }
}

}
