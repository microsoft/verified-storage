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
use crate::pmem::traits_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use deps_hack::PmCopy;
use std::collections::HashMap;
use std::hash::Hash;
use super::*;
use super::recover_v::*;
use super::super::impl_t::*;
use super::super::spec_t::*;
use vstd::set_lib::*;

verus! {

impl<L> ListTableInternalView<L>
    where
        L: PmCopy + LogicalRange + Sized + std::fmt::Debug,
{
    pub(super) proof fn lemma_corresponds_implies_sum_lengths_equals_num_pos_tuples(
        self,
        sm: ListTableStaticMetadata,
        pos: int,
    )
        requires
            sm.valid::<L>(),
            self.row_info_complete(sm),
            self.per_row_info_consistent(sm),
            self.durable_mapping.internally_consistent(sm),
            self.pending_allocations == Seq::<u64>::empty(),
            self.pending_deallocations == Seq::<u64>::empty(),
            self.durable_mapping.as_snapshot().m.dom().finite(),
            0 <= pos <= self.durable_mapping.as_snapshot().m.dom().to_seq().len(),
        ensures
            ({
                let m = self.durable_mapping.as_snapshot().m;
                let s = m.dom().to_seq();
                let prefix = s.take(pos);
                let tups = Set::<(u64, int)>::new(|tup: (u64, int)| {
                    let (head, i) = tup;
                    &&& prefix.contains(head)
                    &&& 0 <= i < m[head].len()
                });
                &&& tups.finite()
                &&& prefix.fold_left(0, |total: int, head: u64| total + m[head].len()) == tups.len()
            }),
        decreases
            pos,
    {
        let m = self.durable_mapping.as_snapshot().m;
        let s = m.dom().to_seq();
        let prefix = s.take(pos);
        let tups = Set::<(u64, int)>::new(|tup: (u64, int)| {
            let (head, i) = tup;
            &&& prefix.contains(head)
            &&& 0 <= i < m[head].len()
        });
        let f = |total: int, head: u64| total + m[head].len();
        lemma_set_to_seq_has_same_length_with_no_duplicates(m.dom());
        if pos > 0 {
            let tups_prev = Set::<(u64, int)>::new(|tup: (u64, int)| {
                let (head, i) = tup;
                &&& s.take(pos - 1).contains(head)
                &&& 0 <= i < m[head].len()
            });
            let tups_cur = Set::<(u64, int)>::new(|tup: (u64, int)| {
                let (head, i) = tup;
                &&& head == s[pos - 1]
                &&& 0 <= i < m[head].len()
            });
            assert(tups_cur.finite() && tups_cur.len() == m[s[pos - 1]].len()) by {
                lemma_int_range(0, m[s[pos - 1]].len() as int);
                lemma_bijection_makes_sets_have_equal_size(
                    set_int_range(0, m[s[pos - 1]].len() as int),
                    tups_cur,
                    |i: int| (s[pos - 1], i),
                    |tup: (u64, int)| tup.1
                );
            }
            self.lemma_corresponds_implies_sum_lengths_equals_num_pos_tuples(sm, pos - 1);
            assert(prefix.drop_last() == s.take(pos - 1));
            assert(prefix.last() == s[pos - 1]);
            assert(prefix.drop_last().fold_left(0, f) == tups_prev.len());
            assert(prefix.fold_left(0, f) == tups_prev.len() + m[s[pos - 1]].len());
            assert(m[s[pos - 1]].len() == tups_cur.len());
            assert(tups_prev + tups_cur =~= tups) by {
                assert forall|tup: (u64, int)| #[trigger] tups.contains(tup) implies (tups_prev + tups_cur).contains(tup) by {
                    let head = tup.0;
                    let j = choose|j: int| 0 <= j < s.take(pos).len() && s.take(pos)[j] == head;
                    if j < pos - 1 {
                        assert(s[j] == head);
                        assert(s.take(pos - 1)[j] == head);
                        assert(s.take(pos - 1).contains(head));
                    }
                }
            }
            assert(tups_prev.disjoint(tups_cur));
            lemma_set_disjoint_lens(tups_prev, tups_cur);
        }
        else {
            assert(prefix =~= Seq::<u64>::empty());
            assert(tups =~= Set::<(u64, int)>::empty());
        }
    }

    pub(super) proof fn lemma_corresponds_implication_for_free_list_length(self, sm: ListTableStaticMetadata)
        requires
            sm.valid::<L>(),
            self.row_info_complete(sm),
            self.per_row_info_consistent(sm),
            self.durable_mapping.internally_consistent(sm),
            self.pending_allocations == Seq::<u64>::empty(),
            self.pending_deallocations == Seq::<u64>::empty(),
        ensures
            ({
                let m = self.durable_mapping.as_snapshot().m;
                &&& m.dom().finite()
                &&& m.dom().to_seq().fold_left(0, |total: int, head: u64| total + m[head].len())
                       == sm.table.num_rows - self.free_list.len()
            }),
    {
        let m = self.durable_mapping.as_snapshot().m;
        let addr_to_len = |total: int, head: u64| total + m[head].len();

        assert forall|pos: int| 0 <= pos < self.free_list.len() implies
            self.row_info.contains_key(#[trigger] self.free_list[pos]) by {
            assert(self.row_info[self.free_list[pos]] is InFreeList);
            assert(self.row_info.contains_key(self.free_list[pos]));
        }

        let free_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr) && self.row_info[row_addr] is InFreeList
        );
        let list_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr) && self.row_info[row_addr] is NowhereFree
        );
        let valid_row_addrs = Set::<u64>::new(
            |row_addr: u64| self.row_info.contains_key(row_addr)
        );
        let list_head_addrs = Set::<u64>::new(
            |row_addr: u64| self.durable_mapping.row_info.contains_key(row_addr) &&
                            self.durable_mapping.row_info[row_addr].pos == 0
        );

        assert(m.dom() == self.durable_mapping.list_elements.dom());
        let list_heads = m.dom().to_seq();

        assert(valid_row_addrs.finite() && valid_row_addrs.len() == sm.table.num_rows) by {
            assert(valid_row_addrs =~= Set::<u64>::new(|row_addr: u64| sm.table.validate_row_addr(row_addr)));
            sm.table.lemma_valid_row_set_len();
        }
        assert(free_row_addrs.finite()) by {
            vstd::set_lib::lemma_len_subset(free_row_addrs, valid_row_addrs);
        }
        assert(list_row_addrs.finite()) by {
            vstd::set_lib::lemma_len_subset(list_row_addrs, valid_row_addrs);
        }
        assert(list_head_addrs.finite()) by {
            vstd::set_lib::lemma_len_subset(list_head_addrs, valid_row_addrs);
        }
        assert(list_head_addrs =~= m.dom());

        assert(valid_row_addrs.len() == free_row_addrs.len() + list_row_addrs.len()) by {
            assert(free_row_addrs.disjoint(list_row_addrs));
            assert(free_row_addrs + list_row_addrs =~= valid_row_addrs);
            vstd::set_lib::lemma_set_disjoint_lens(free_row_addrs, list_row_addrs);
        }

        assert(free_row_addrs.len() == self.free_list.len()) by {
            assert(self.free_list.to_set() =~= free_row_addrs);
            self.free_list.unique_seq_to_set();
        }

        let tups = Set::<(u64, int)>::new(|tup: (u64, int)| {
            let (head, i) = tup;
            &&& list_heads.contains(head)
            &&& 0 <= i < m[head].len()
        });
        assert(tups.finite() && list_heads.fold_left(0, addr_to_len) == tups.len()) by {
            self.lemma_corresponds_implies_sum_lengths_equals_num_pos_tuples(sm, list_heads.len() as int);
            assert(list_heads.take(list_heads.len() as int) =~= list_heads);
        }

        assert(tups.len() == list_row_addrs.len()) by {
            let f = |tup: (u64, int)| self.durable_mapping.list_info[tup.0][tup.1];
            let g = |row_addr: u64| (self.durable_mapping.row_info[row_addr].head,
                                     self.durable_mapping.row_info[row_addr].pos);
            assert forall|tup: (u64, int)| #[trigger] tups.contains(tup)
                implies list_row_addrs.contains(f(tup)) && g(f(tup)) == tup by {
                let (head, i) = tup;
                assert(list_heads.contains(head));
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), head);
                assert(m.dom().contains(head));
                assert(self.durable_mapping.list_info.contains_key(head));
                assert(self.row_info.contains_key(self.durable_mapping.list_info[head][i]));
            }
            assert forall|row_addr: u64| #[trigger] list_row_addrs.contains(row_addr)
                implies tups.contains(g(row_addr)) && f(g(row_addr)) == row_addr by {
                assert(self.durable_mapping.row_info.contains_key(row_addr));
                let (head, i) = g(row_addr);
                assert(self.durable_mapping.list_info.contains_key(head));
                assert(0 <= i < self.durable_mapping.list_info[head].len());
                assert(self.durable_mapping.list_info[head][i] == row_addr);
                lemma_set_to_seq_contains_iff_set_contains(m.dom(), head);
                assert(list_heads.contains(head));
            }
            lemma_bijection_makes_sets_have_equal_size(tups, list_row_addrs, f, g);
        }
    }
}

}

