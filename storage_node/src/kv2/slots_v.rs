#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::calc_macro::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::util_v::*;
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
    pub(super) proof fn lemma_filtering_keys_doesnt_affect_fold(self, pos: int)
        requires
            self.status@ is ComponentsDontCorrespond,
            self.inv(),
            self.keys@.durable.item_addrs() == self.items@.durable.m.dom(),
            self.keys@.durable.list_addrs() == self.lists@.durable.m.dom(),
            self@.durable.m.dom().finite(),
            0 <= pos <= self@.durable.m.dom().to_seq().len(),
        ensures
            ({
                let m = self@.durable.m;
                let kseq = m.dom().to_seq();
                let kseq_truncated = kseq.take(pos);
                let kseq_truncated_and_filtered =
                    kseq_truncated.filter(|k: K| self.keys@.durable.key_info[k].list_addr != 0);
                kseq_truncated_and_filtered.fold_left(0, |total: int, k: K| total + m[k].1.len()) ==
                    kseq_truncated.fold_left(0, |total: int, k: K| total + m[k].1.len())
            }),
        decreases
            pos,
    {
        let keys = self.keys@.durable;
        let items = self.items@.durable;
        let lists = self.lists@.durable;
        let m = self@.durable.m;
        let kseq = m.dom().to_seq();
        let kseq_truncated = kseq.take(pos);
        let filt = |k: K| keys.key_info[k].list_addr != 0;

        if pos == 0 {
            return;
        }

        assert(kseq_truncated.drop_last() =~= kseq.take(pos - 1));
        assert(kseq_truncated.last() == kseq_truncated[pos - 1]);

        self.lemma_filtering_keys_doesnt_affect_fold(pos - 1);

        let last_key = kseq_truncated.last();
        lemma_set_to_seq_contains_iff_set_contains(m.dom(), last_key);

        if keys.key_info[last_key].list_addr == 0 {
            assert(kseq_truncated.filter(filt) == kseq_truncated.drop_last().filter(filt)) by {
                reveal(Seq::filter);
            }
        }
        else {
            assert(kseq_truncated.filter(filt) ==
                   kseq_truncated.drop_last().filter(filt).push(kseq_truncated.last())) by {
                reveal(Seq::filter);
            }
            assert(kseq_truncated.filter(filt).drop_last() == kseq_truncated.drop_last().filter(filt));
            assert(kseq_truncated.filter(filt).last() == kseq_truncated.last());
        }
    }

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
        let keys = self.keys@.durable;
        let items = self.items@.durable;
        let lists = self.lists@.durable;
        let m = self@.durable.m;
        let list_used_slots = lists.m.dom().to_seq().fold_left(
            0, |total: int, row_addr: u64| total + lists.m[row_addr].len()
        );

        assert(m == Map::<K, (I, Seq<L>)>::new(
            |k: K| keys.key_info.dom().contains(k),
            |k: K| (items.m[keys.key_info[k].item_addr],
                    if keys.key_info[k].list_addr == 0 { Seq::<L>::empty() }
                    else { lists.m[keys.key_info[k].list_addr] }),
        ));

        assert(self@.durable.num_list_elements() ==
               m.dom().to_seq().fold_left(0, |total: int, k: K| total + m[k].1.len()));

        assert(m.dom() =~= keys.key_info.dom());

        let kseq = m.dom().to_seq();
        let kseq_filtered = kseq.filter(|k: K| keys.key_info[k].list_addr != 0);
        assert(kseq_filtered.fold_left(0, |total: int, k: K| total + m[k].1.len()) ==
               kseq.fold_left(0, |total: int, k: K| total + m[k].1.len())) by {
            self.lemma_filtering_keys_doesnt_affect_fold(kseq.len() as int);
            assert(kseq =~= kseq.take(kseq.len() as int));
        }

        assume(kseq.fold_left(0, |total: int, k: K| total + m[k].1.len()) == list_used_slots);
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
