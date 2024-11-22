use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::*;

verus! {
    // Multi-indexing of a sequence.
    pub open spec fn valid_index<T>(s: Seq<T>, i: int) -> bool {
        0 <= i < s.len()
    }

    pub open spec fn valid_indexes<T>(s: Seq<T>, indexes: Seq<int>) -> bool {
        forall |i: int| 0 <= i < indexes.len() ==> #[trigger] valid_index(s, indexes[i])
    }

    pub proof fn valid_indexes_permute<T>(s: Seq<T>, idx1: Seq<int>, idx2: Seq<int>)
        requires
            valid_indexes(s, idx1),
            idx1.to_multiset() == idx2.to_multiset(),
        ensures
            valid_indexes(s, idx2)
    {
        assert forall |i: int| 0 <= i < idx2.len() implies #[trigger] valid_index(s, idx2[i]) by {
            let idx = idx2[i];
            idx1.to_multiset_ensures();
            idx2.to_multiset_ensures();
            assert(idx2.to_multiset().count(idx) > 0);
        }
    }

    // WSeq is just a wrapper for Seq that provides better notation
    // for a multi-index operator through its spec_index().
    pub struct WSeq<T> {
        pub s: Seq<T>,
    }

    impl<T> WSeq<T> {
        pub open spec fn spec_index(self, idx: Seq<int>) -> Seq<T>
            recommends
                valid_indexes(self.s, idx)
        {
            idx.map_values(|a: int| self.s[a])
        }
    }

    #[allow(non_snake_case)]
    pub open spec fn S<T>(s: Seq<T>) -> WSeq<T>
    {
        WSeq{
            s: s
        }
    }

    pub proof fn indexes_first<T>(s: Seq<T>, indexes: Seq<int>)
        requires
            indexes.len() > 0,
            valid_indexes(s, indexes),
        ensures
            S(s)[indexes] =~= seq![s[indexes.first()]] + S(s)[indexes.drop_first()],
            valid_index(s, indexes.first()),
            valid_indexes(s, indexes.drop_first()),
    {
    }

    pub proof fn indexes_permute<T>(s: Seq<T>, idx1: Seq<int>, idx2: Seq<int>)
        requires
            valid_indexes(s, idx1),
            idx1.to_multiset() == idx2.to_multiset(),
        ensures
            S(s)[idx1].to_multiset() =~= S(s)[idx2].to_multiset()
        decreases
            idx1.len()
    {
        idx1.to_multiset_ensures();
        idx2.to_multiset_ensures();
        S(s)[idx1].to_multiset_ensures();
        S(s)[idx2].to_multiset_ensures();
        if idx1.len() > 0 {
            let i = idx1.first();
            assert(idx1.to_multiset().contains(i));
            let idx2pos = idx2.index_of(i);

            let idx1rec = idx1.remove(0);
            let idx2rec = idx2.remove(idx2pos);

            indexes_permute(s, idx1rec, idx2rec);
            lemma_seq_union_to_multiset_commutative(seq![s[i]], S(s)[idx1rec]);
            lemma_multiset_commutative(S(s)[idx1rec], seq![s[i]]);

            seq![s[i]].to_multiset_ensures();
            assert(seq![s[i]].first() == s[i]);

            assert(S(s)[idx1] =~= seq![s[i]] + S(s)[idx1rec]);
            assert(S(s)[idx2rec] =~= S(s)[idx2].remove(idx2pos));
        }
    }

    // sum
    pub closed spec fn sum(l: Seq<nat>) -> nat {
        l.fold_right(|i, s: nat| { s+i as nat }, 0)
    }

    pub proof fn sum_permute(s1: Seq<nat>, s2: Seq<nat>)
        requires
            s1.to_multiset() == s2.to_multiset()
        ensures
            sum(s1) == sum(s2)
    {
        lemma_fold_right_permutation(s1, s2, |i, s: nat| { s+i as nat }, 0)
    }

    pub proof fn sum_concat(s1: Seq<nat>, s2: Seq<nat>)
        ensures
            sum(s1+s2) == sum(s1) + sum(s2)
    {
        let s = s1+s2;
        assert(s1 == s.subrange(0, s1.len() as int));
        assert(s2 == s.subrange(s1.len() as int, s.len() as int));
        s.lemma_fold_right_split(|i, s: nat| { s+i as nat }, 0, s1.len() as int);
        s1.lemma_fold_right_commute_one(sum(s2), |i, s: nat| { s+i as nat }, 0);
    }

    pub proof fn sum_remove(s: Seq<nat>, i: int)
        requires
            0 <= i < s.len()
        ensures
            sum(s) == s[i] + sum(s.remove(i))
    {
        let s1 = s.subrange(0, i);
        let s2 = s.subrange(i, s.len() as int);
        assert(s == s1+s2);

        assert(s.remove(i) == s1 + s2.drop_first());

        sum_concat(s1, s2);
        assert(sum(s) == sum(s1) + sum(s2));
        sum_concat(s1, s2.drop_first());
        assert(sum(s.remove(i)) == sum(s1) + sum(s2.drop_first()));

        s2.lemma_fold_right_alt(|i, s: nat| { s+i as nat }, 0);
        s2.drop_first().lemma_fold_right_alt(|i, s: nat| { s+i as nat }, 0);
        assert(sum(s2) == s2[0] + sum(s2.drop_first()));
    }

    pub proof fn sum_indexes(s: Seq<nat>, idx: Seq<int>)
        requires
            idx.no_duplicates(),
            valid_indexes(s, idx),
        ensures
            sum(S(s)[idx]) <= sum(s)
    {
        idx.lemma_sort_ensures();
        let idx_sorted = idx.sort();
        idx.lemma_multiset_has_no_duplicates();
        idx_sorted.lemma_multiset_has_no_duplicates_conv();

        valid_indexes_permute(s, idx, idx_sorted);
        sum_indexes_helper(s, idx_sorted);
        indexes_permute(s, idx, idx_sorted);
        sum_permute(S(s)[idx], S(s)[idx_sorted]);
    }

    pub proof fn sum_indexes_helper(s: Seq<nat>, indexes: Seq<int>)
        requires
            indexes.no_duplicates(),
            valid_indexes(s, indexes),
            sorted_by(indexes, |x: int, y: int| x <= y),
        ensures
            sum(S(s)[indexes]) <= sum(s)
        decreases
            s.len()
    {
        if indexes.len() > 0 {
            let i = indexes.last();
            assert(valid_index(s, i));

            let s0 = s.subrange(0, i);
            let s1 = s.subrange(i, s.len() as int);
            assert(s == s0 + s1);
            sum_concat(s0, s1);

            assert forall |j: int| 0 <= j < indexes.drop_last().len() implies #[trigger] valid_index(s0, indexes.drop_last()[j]) by {
                let idx = indexes.drop_last()[j];
                assert(valid_index(s, idx));
                assert((|x: int, y: int| x <= y)(indexes[j], indexes.last()));
            }
            sum_indexes_helper(s0, indexes.drop_last());

            assert forall |j: int| 0 <= j < indexes.drop_last().len() implies 0 <= #[trigger] indexes.drop_last()[j] < s0.len() by {
                assert(valid_index(s0, indexes.drop_last()[j]));
            }

            reveal_with_fuel(Seq::fold_right, 2);
            sum_remove(s1, 0);
            assert(S(s0)[indexes.drop_last()] + S(s)[seq![i]] == S(s)[indexes]);
            sum_concat(S(s0)[indexes.drop_last()], S(s)[seq![i]]);
        }
    }

    // popcnt
    #[verifier::inline]
    pub open spec fn _popcnt_byte(a: u8) -> nat {
        let p0 = 1u8 & (a >> 0u8);
        let p1 = 1u8 & (a >> 1u8);
        let p2 = 1u8 & (a >> 2u8);
        let p3 = 1u8 & (a >> 3u8);
        let p4 = 1u8 & (a >> 4u8);
        let p5 = 1u8 & (a >> 5u8);
        let p6 = 1u8 & (a >> 6u8);
        let p7 = 1u8 & (a >> 7u8);
        let sum = add(p0, add(p1, add(p2, add(p3, add(p4, add(p5, add(p6, p7)))))));
        sum as nat
    }

    pub open spec fn popcnt_byte(a: u8) -> nat {
        _popcnt_byte(a)
    }

    spec fn popcnt_seq(l: Seq<u8>) -> Seq<nat> {
        l.map_values(|v: u8| popcnt_byte(v))
    }

    pub closed spec fn popcnt(l: Seq<u8>) -> nat {
        sum(popcnt_seq(l))
    }

    proof fn popcnt_remove(l: Seq<u8>, i: int)
        requires
            0 <= i < l.len()
        ensures
            popcnt(l) == popcnt_byte(l[i]) + popcnt(l.remove(i))
    {
        sum_remove(popcnt_seq(l), i);
        assert(popcnt_seq(l).remove(i) == popcnt_seq(l.remove(i)));
    }

    proof fn popcnt_indexes(s: Seq<u8>, idx: Seq<int>)
        requires
            valid_indexes(s, idx)
        ensures
            popcnt_seq(S(s)[idx]) =~= S(popcnt_seq(s))[idx]
        decreases
            idx.len()
    {
        if idx.len() > 0 {
            popcnt_indexes(s, idx.drop_first());
            indexes_first(s, idx);
            assert(popcnt_seq(seq![s[idx[0]]] + S(s)[idx.drop_first()]) =~=
                   seq![popcnt_byte(s[idx[0]])] + popcnt_seq(S(s)[idx.drop_first()]));
        }
    }

    pub proof fn popcnt_indexes_le(s: Seq<u8>, idx: Seq<int>)
        requires
            idx.no_duplicates(),
            valid_indexes(s, idx),
        ensures
            popcnt(S(s)[idx]) <= popcnt(s)
    {
        assert(forall |i: int| 0 <= i < idx.len() ==> valid_index(s, idx[i]) ==> #[trigger] valid_index(popcnt_seq(s), idx[i]));
        sum_indexes(popcnt_seq(s), idx);
        popcnt_indexes(s, idx);
    }

    pub proof fn popcnt_index_le(s: Seq<u8>, idx: int)
        requires
            valid_index(s, idx)
        ensures
            popcnt_byte(s[idx]) <= popcnt(s)
    {
        popcnt_remove(s, idx);
    }

    pub proof fn popcnt_ext_le(s1: Seq<u8>, s2: Seq<u8>)
        requires
            s1.len() == s2.len(),
            forall |i: int| 0 <= i < s1.len() ==> #[trigger] popcnt_byte(s1[i]) <= popcnt_byte(s2[i]),
        ensures
            popcnt(s1) <= popcnt(s2)
        decreases
            s1.len(),
    {
        if s1.len() > 0 {
            popcnt_remove(s1, 0);
            popcnt_remove(s2, 0);
            popcnt_ext_le(s1.drop_first(), s2.drop_first());
        }
    }

    // Bitwise XOR and AND for sequences
    pub open spec fn xor(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
        a.zip_with(b).map_values(|v: (u8, u8)| v.0 ^ v.1)
    }

    pub open spec fn and(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
        a.zip_with(b).map_values(|v: (u8, u8)| v.0 & v.1)
    }

    pub proof fn byte_xor_xor(a: u8, b: u8)
        ensures
            (a^b) ^ a == b,
    {
        assert((a^b) ^ a == b) by (bit_vector)
    }

    pub proof fn byte_and_zero(a: u8)
        ensures
            a & 0 == 0
    {
        assert(a & 0 == 0) by (bit_vector)
    }

    pub proof fn byte_xor_mask_popcnt_byte_le(a: u8, mask: u8, b: u8)
        ensures
            popcnt_byte((a ^ (mask & b)) ^ a) <= popcnt_byte(b)
    {
        assert(_popcnt_byte((a ^ (mask & b)) ^ a) <= _popcnt_byte(b)) by (bit_vector);
    }

    pub proof fn list_xor_xor(a: Seq<u8>, b: Seq<u8>)
        requires
            a.len() == b.len(),
        ensures
            xor(xor(a, b), a) =~= b,
        decreases
            a.len()
    {
        if a.len() > 0 {
            byte_xor_xor(a[0], b[0]);
            list_xor_xor(a.drop_first(), b.drop_first());
            assert(b == seq![b[0]] + b.drop_first());
        }
    }

    pub proof fn xor_indexes(s1: Seq<u8>, s2: Seq<u8>, idx: Seq<int>)
        requires
            s1.len() == s2.len(),
            valid_indexes(s1, idx),
        ensures
            xor(S(s1)[idx], S(s2)[idx]) =~= S(xor(s1, s2))[idx]
        decreases
            idx.len()
    {
        if idx.len() > 0 {
            xor_indexes(s1, s2, idx.drop_first());
            assert(idx =~= seq![idx.first()] + idx.drop_first());
            assert(S(xor(s1, s2))[seq![idx.first()] + idx.drop_first()] =~=
                   seq![xor(s1, s2)[idx.first()]] + S(xor(s1, s2))[idx.drop_first()]);
            assert(valid_index(s1, idx.first()));
        }
    }

    pub proof fn xor_comm(s1: Seq<u8>, s2: Seq<u8>)
        requires
            s1.len() == s2.len()
        ensures
            xor(s1, s2) =~= xor(s2, s1)
        decreases
            s1.len()
    {
        if s1.len() > 0 {
            let a = s1.first();
            let b = s2.first();
            assert(a^b == b^a) by (bit_vector);
            xor_comm(s1.drop_first(), s2.drop_first());
            assert(xor(s1, s2) == seq![xor(s1, s2).first()] + xor(s1, s2).drop_first());
            assert(xor(s1, s2).drop_first() == xor(s1.drop_first(), s2.drop_first()));
        }
    }

    proof fn popcnt_byte_and(a: u8, b: u8)
        ensures
            popcnt_byte(a&b) <= popcnt_byte(a),
            popcnt_byte(a&b) <= popcnt_byte(b),
    {
        assert(_popcnt_byte(a&b) <= _popcnt_byte(a)) by (bit_vector);
        assert(_popcnt_byte(a&b) <= _popcnt_byte(b)) by (bit_vector);
    }

    pub proof fn popcnt_and(a: Seq<u8>, b: Seq<u8>)
        requires
            a.len() == b.len(),
        ensures
            popcnt(and(a, b)) <= popcnt(a),
            popcnt(and(a, b)) <= popcnt(b),
        decreases
            a.len(),
    {
        if a.len() > 0 {
            popcnt_byte_and(a[0], b[0]);
            popcnt_and(a.drop_first(), b.drop_first());
            popcnt_remove(a, 0);
            popcnt_remove(b, 0);
            popcnt_remove(and(a, b), 0);
            assert(and(a, b).drop_first() == and(a.drop_first(), b.drop_first()));
        }
    }

    pub proof fn popcnt_byte_zero(a: u8)
        requires
            popcnt_byte(a) == 0
        ensures
            a == 0
    {
        assert(_popcnt_byte(a) == 0 ==> a == 0) by (bit_vector);
    }

    pub proof fn xor_byte_zero(a: u8)
        ensures
            a ^ 0u8 == a,
    {
        assert(a ^ 0 == a) by (bit_vector);
    }

    pub proof fn xor_zeroes(a: Seq<u8>, b: Seq<u8>)
        requires
            a.len() == b.len(),
            popcnt(b) == 0,
        ensures
            xor(a, b) =~= a,
        decreases
            a.len()
    {
        if a.len() > 0 {
            popcnt_remove(b, 0);
            popcnt_byte_zero(b.first());
            xor_byte_zero(a.first());
            xor_zeroes(a.drop_first(), b.drop_first());
            assert(a == seq![a.first()] + a.drop_first());
        }
    }

    // Sequence of zeroes, for proving the existence of a sequence with a zero popcnt.
    pub open spec fn u8_zeroes(len: nat) -> Seq<u8> {
        Seq::new(len, |i: int| 0)
    }

    proof fn sum_nat_zeroes(len: nat)
        ensures
            sum(Seq::new(len, |i: int| 0nat)) == 0
        decreases
            len
    {
        if len > 0 {
            let l = Seq::new(len, |i: int| 0nat);
            let l1 = Seq::new((len-1) as nat, |i: int| 0nat);

            sum_nat_zeroes(l1.len());
            assert(l1 == l.drop_last());
        }
    }

    pub proof fn popcnt_u8_zeroes(len: nat)
        ensures
            popcnt(u8_zeroes(len)) == 0,
            u8_zeroes(len).len() == len,
    {
        assert(_popcnt_byte(0) == 0) by (bit_vector);
        assert(u8_zeroes(len).map_values(|v: u8| popcnt_byte(v)) == Seq::new(len, |i: int| 0nat));
        sum_nat_zeroes(len);
    }

    // Top-level lemma: definition of Hamming distance, and proof that the
    // Hamming distance of a subset of indexes in a sequence is bounded by
    // the Hamming distance of the entire sequence.
    pub open spec fn hamming(a: Seq<u8>, b: Seq<u8>) -> nat {
        popcnt(xor(a, b))
    }

    pub proof fn hamming_indexes(s1: Seq<u8>, s2: Seq<u8>, idx: Seq<int>)
        requires
            s1.len() == s2.len(),
            idx.no_duplicates(),
            valid_indexes(s1, idx),
        ensures
            hamming(S(s1)[idx], S(s2)[idx]) <= hamming(s1, s2),
    {
        xor_indexes(s1, s2, idx);
        assert(forall |i: int| 0 <= i < idx.len() ==> valid_index(s1, idx[i]) ==> #[trigger] valid_index(xor(s1, s2), idx[i]));
        popcnt_indexes_le(xor(s1, s2), idx);
    }
}
