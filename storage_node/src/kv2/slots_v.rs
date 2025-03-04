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
    pub(super) proof fn lemma_used_list_slots_correspond(self)
        requires
            self.status@ is ComponentsDontCorrespond,
            self.inv(),
            self.keys@.durable.item_addrs() == self.items@.durable.m.dom(),
            self.keys@.durable.list_addrs() == self.lists@.durable.m.dom(),
        ensures
            self@.durable.num_list_elements() ==
                self.lists@.durable.m.dom().to_seq().fold_left(
                    0, |total: int, row_addr: u64| total + self.lists@.durable.m[row_addr].len()
                ),
    {
        let list_used_slots = self.lists@.durable.m.dom().to_seq().fold_left(
            0, |total: int, row_addr: u64| total + self.lists@.durable.m[row_addr].len()
        );

        assume(self@.durable.num_list_elements() == list_used_slots);
    }

    pub(super) proof fn lemma_used_slots_correspond(self)
        requires
            self.status@ is ComponentsDontCorrespond,
            self.inv(),
            self.keys@.durable.item_addrs() == self.items@.durable.m.dom(),
            self.keys@.durable.list_addrs() == self.lists@.durable.m.dom(),
        ensures
            self@.durable.num_keys() == self.keys@.durable.key_info.dom().len(),
            self@.durable.num_keys() == self.items@.durable.m.dom().len(),
            self@.durable.num_list_elements() ==
                self.lists@.durable.m.dom().to_seq().fold_left(
                    0, |total: int, row_addr: u64| total + self.lists@.durable.m[row_addr].len()
                ),
    {
        assert(self@.durable.m.dom() =~= self.keys@.durable.key_info.dom());

        assert(self.keys@.durable.item_info.dom().len() == self.keys@.durable.key_info.dom().len()) by {
            self.keys.lemma_valid_implications(self.journal@);
            self.keys@.durable.lemma_valid_implies_num_keys_equals_num_items();
        }

        self.lemma_used_list_slots_correspond();
    }
}

}
