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
            self.inv_components_finite(),
            self.inv_components_correspond(),
            self.keys@.durable.valid(),
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
        let list_addr_seq = lists.m.dom().to_seq();
        let accumulate_row_addr = |total: int, row_addr: u64| total + lists.m[row_addr].len();
        let list_used_slots = list_addr_seq.fold_left(0, accumulate_row_addr);
        let accumulate_key = |total: int, k: K| total + m[k].1.len();
        assert(self@.durable.num_list_elements() == m.dom().to_seq().fold_left(0, accumulate_key));

        assert(m.dom() =~= keys.key_info.dom());

        let kseq = m.dom().to_seq();
        let key_has_list = |k: K| keys.key_info[k].list_addr != 0;
        let keys_with_lists_seq = kseq.filter(key_has_list);

        assert(kseq.fold_left(0, accumulate_key) == keys_with_lists_seq.fold_left(0, accumulate_key)) by {
            self.lemma_filtering_keys_doesnt_affect_fold(kseq.len() as int);
            assert(kseq =~= kseq.take(kseq.len() as int));
        }

        let key_to_list_addr = |k: K| keys.key_info[k].list_addr;
        let keys_with_lists_seq_mapped = keys_with_lists_seq.map_values(key_to_list_addr);

        assert(keys_with_lists_seq.fold_left(0, accumulate_key) ==
               keys_with_lists_seq_mapped.fold_left(0, accumulate_row_addr)) by {
            assert forall|total: int, k: K| keys_with_lists_seq.contains(k) implies
                #[trigger] accumulate_key(total, k) == accumulate_row_addr(total, key_to_list_addr(k)) by {
                assert(keys.key_info[k].list_addr != 0);
                lemma_if_filter_contains_then_original_contains(kseq, key_has_list, k);
                assert(kseq.contains(k));
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), k);
                assert(keys.key_info.dom().contains(k));
                assert(m[k].1 == lists.m[keys.key_info[k].list_addr]);
                assert(accumulate_key(total, k) == accumulate_row_addr(total, key_to_list_addr(k)));
            }
            lemma_fold_equivalent_to_map_fold::<K, u64, int>(
                0, keys_with_lists_seq, key_to_list_addr, accumulate_key, accumulate_row_addr
            );
        }

        assert(keys_with_lists_seq_mapped.to_set() =~= list_addr_seq.to_set()) by {
            let s1 = keys_with_lists_seq_mapped;
            let s2 = list_addr_seq;
            assert forall|row_addr: u64| s1.contains(row_addr) implies s2.contains(row_addr) by {
                let i = choose|i: int| 0 <= i < s1.len() && s1[i] == row_addr;
                let k = keys_with_lists_seq[i];
                assert(keys.key_info[k].list_addr == row_addr);
                lemma_if_filter_contains_then_original_contains(kseq, key_has_list, k);
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), k);
                lemma_set_to_seq_contains_iff_set_contains(lists.m.dom(), row_addr);
            }
            assert forall|row_addr: u64| s2.contains(row_addr) implies s1.contains(row_addr) by {
                lemma_set_to_seq_contains_iff_set_contains(lists.m.dom(), row_addr);
                assert(lists.m.contains_key(row_addr));
                assert(keys.list_info.contains_key(row_addr));
                let k: K = keys.list_info[row_addr];
                assert(m.contains_key(k));
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), k);
                assert(kseq.contains(k));
                assert(keys_with_lists_seq.contains(k));
                let i = choose|i: int| 0 <= i < keys_with_lists_seq.len() && keys_with_lists_seq[i] == k;
                assert(s1[i] == row_addr);
            }
        }

        assert(list_addr_seq.no_duplicates()) by {
            lemma_set_to_seq_has_same_length_with_no_duplicates(lists.m.dom());
        }

        assert(keys_with_lists_seq.no_duplicates()) by {
            lemma_set_to_seq_has_same_length_with_no_duplicates(m.dom());
            lemma_filter_preserves_no_duplicates(kseq, key_has_list);
        }

        assert(keys_with_lists_seq_mapped.no_duplicates()) by {
            let s = keys_with_lists_seq_mapped;
            assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {
                let k1 = keys_with_lists_seq[i];
                let k2 = keys_with_lists_seq[j];
                assert(k1 != k2);
                lemma_if_filter_contains_then_original_contains(kseq, key_has_list, k1);
                lemma_if_filter_contains_then_original_contains(kseq, key_has_list, k2);
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), k1);
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), k2);
            }
        }

        let accumulate_row_addr_converted = convert_foldl_to_foldr(accumulate_row_addr);
        assert(keys_with_lists_seq_mapped.fold_left(0, accumulate_row_addr) ==
               list_addr_seq.fold_left(0, accumulate_row_addr)) by {
            lemma_two_seqs_with_no_duplicates_and_same_to_set_are_permutations::<u64>(keys_with_lists_seq_mapped,
                                                                                      list_addr_seq);
            lemma_commutative_foldl_equivalent_to_corresponding_foldr(keys_with_lists_seq_mapped, 0,
                                                                      accumulate_row_addr);
            lemma_commutative_foldl_equivalent_to_corresponding_foldr(list_addr_seq, 0, accumulate_row_addr);
            vstd::seq_lib::lemma_fold_right_permutation::<u64, int>(
                keys_with_lists_seq_mapped, list_addr_seq, accumulate_row_addr_converted, 0
            );
        }
    }

    pub(super) proof fn lemma_used_slots_correspond(self)
        requires
            self.inv_components_finite(),
            self.inv_components_correspond(),
            self.inv_components_valid(),
        ensures
            self@.durable.num_keys() == self.keys@.durable.key_info.dom().len(),
            self@.durable.num_keys() == self.items@.durable.m.dom().len(),
            self@.durable.num_list_elements() ==
                self.lists@.durable.m.dom().to_seq().fold_left(
                    0, |total: int, row_addr: u64| total + self.lists@.durable.m[row_addr].len()
                ),
    {
        assert(self@.durable.m.dom() =~= self.keys@.durable.key_info.dom());

        self.keys.lemma_valid_implications(self.journal@);

        assert(self.keys@.durable.item_info.dom().len() == self.keys@.durable.key_info.dom().len()) by {
            self.keys@.durable.lemma_valid_implies_num_keys_equals_num_items();
        }

        self.lemma_used_list_slots_correspond();
    }

    pub(super) proof fn lemma_using_space_for_transaction_operation_maintains_invariant(
        self,
        old_self: Self,
    )
        requires
            self.sm@.valid::<K, I, L>(),
            old_self.sm == self.sm,
            self.used_transaction_operation_slots@ == old_self.used_transaction_operation_slots@ + 1,
            old_self.journal@.remaining_capacity >=
                (old_self.sm@.max_operations_per_transaction - old_self.used_transaction_operation_slots@) *
                Self::spec_space_needed_for_transaction_operation(),
            self.journal@.remaining_capacity >=
                old_self.journal@.remaining_capacity - Self::spec_space_needed_for_transaction_operation(),
        ensures
            self.journal@.remaining_capacity >=
                (self.sm@.max_operations_per_transaction - self.used_transaction_operation_slots@) *
                Self::spec_space_needed_for_transaction_operation(),
    {
        let a = old_self.sm@.max_operations_per_transaction;
        let b = old_self.used_transaction_operation_slots@;
        let c = Self::spec_space_needed_for_transaction_operation();
        assert((a - b) * c - c == (a - (b + 1)) * c) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(c as int, a - b, 1);
        }
    }

    /*
    pub(super) proof fn lemma_using_space_for_transaction_operation_maintains_invariant(
        self,
        jv: JournalView,
        old_self: Self,
        old_jv: JournalView,
    )
        requires
            self.sm@.valid::<K, I, L>(),
            old_self.sm == self.sm,
            self.used_transaction_operation_slots@ == old_self.used_transaction_operation_slots@ + 1,
            old_jv.remaining_capacity >=
                (old_self.sm@.max_operations_per_transaction - old_self.used_transaction_operation_slots@) *
                Self::spec_space_needed_for_transaction_operation(),
            jv.remaining_capacity >= old_jv.remaining_capacity - Self::spec_space_needed_for_transaction_operation(),
        ensures
            jv.remaining_capacity >=
                (self.sm@.max_operations_per_transaction - self.used_transaction_operation_slots@) *
                Self::spec_space_needed_for_transaction_operation(),
    {
        let a = old_self.sm@.max_operations_per_transaction;
        let b = old_self.used_transaction_operation_slots@;
        let c = Self::spec_space_needed_for_transaction_operation();
        assert((a - b) * c - c == (a - (b + 1)) * c) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(c as int, a - b, 1);
        }
    }
    */

}

}
