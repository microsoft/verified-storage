use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;

verus! {

// vstd does not implement max for Seq<nat>
pub open spec fn nat_seq_max(seq: Seq<nat>) -> nat 
    recommends 
        0 < seq.len(),
    decreases seq.len()
{
    if seq.len() == 1 {
        seq[0]
    } else if seq.len() == 0 {
        0
    } else {
        let later_max = nat_seq_max(seq.drop_first());
        if seq[0] >= later_max {
            seq[0]
        } else {
            later_max
        }
    }
}

// This lemma proves that a subrange of a subrange is equal to just obtaining the final subrange using its 
// absolute start index. This is obvious and requires no body, but having a dedicated lemma helps
// Z3 establish the equality
// TODO: do this about subranges rather than extract_bytes -- should be equivalent and more useful
// TODO: move extract_bytes into this file
pub proof fn lemma_subrange_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
requires 
    start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
ensures 
    ({
        let start_offset = start2 - start1;
        extract_bytes(extract_bytes(mem, start1, len1), start_offset as nat, len2) =~= 
            extract_bytes(mem, start2, len2)
    })
{}

// This helper lemma helps us prove that flattening a 2D sequence
// is equivalent to concatenating the last sequence to all prior
// sequences after flattening them.
pub proof fn lemma_seqs_flatten_equal_suffix(s: Seq<Seq<u8>>)
    requires
        s.len() >= 1
    ensures 
        ({
            let last = s[s.len() - 1];
            let prefix = s.subrange(0, s.len() - 1);
            s.flatten() == prefix.flatten() + last
        })
    decreases s.len()
{
    if s.len() == 1 {
        let last = s[0];
        assert(s == seq![last]);
        seq![last].lemma_flatten_one_element();
        assert(seq![last].flatten() == last);
    }
    else {
        let first = s[0];
        let last = s[s.len() - 1];
        let middle = s.subrange(0, s.len() - 1).drop_first();
        let suffix = s.drop_first();

        assert(middle == suffix.subrange(0, suffix.len() - 1));

        lemma_seqs_flatten_equal_suffix(suffix);
        assert(suffix.flatten() == middle.flatten() + last);
        assert(first + suffix.flatten() == first + middle.flatten() + last);
    }
}

pub proof fn lemma_injective_map_is_invertible<K, V>(map: Map<K, V>)
    requires 
        map.is_injective(),
    ensures 
        map == map.invert().invert()
{
    map.lemma_invert_is_injective();
    map.invert().lemma_invert_is_injective();
    assert(map.invert().dom() == map.values());
    lemma_injective_map_inverse(map);
    lemma_injective_map_inverse(map.invert());
    assert(map =~= map.invert().invert());
}

pub proof fn lemma_injective_map_inverse<K, V>(map: Map<K, V>)
    requires 
        map.is_injective()
    ensures 
        forall |k: K| map.contains_key(k) ==> {
            let v = map[k];
            map.invert()[v] == k
        }
{
    assert forall |k: K| map.contains_key(k) implies {
        let v = map[k];
        map.invert()[v] == k
    } by {
        let v = map[k];
        if map.invert()[v] != k {
            // if v maps to a different key in the map.invert(), then it must have been the case 
            // that multiple keys mapped to the same value in the original map. but `map` is injective
            // so that cannot be true.
            let k_prime = map.invert()[v];
            assert(map.contains_pair(k, v));
            assert(map.contains_pair(k_prime, v));
            assert(k != k_prime);
            assert(false);
        }
    }
}

// This lemma proves that a sequence with no duplicates whose values are in the range [min, max)
// has a length less than or equal to the difference between min and max.
pub proof fn lemma_seq_len_when_no_dup_and_all_values_in_range(s: Seq<int>, min: int, max: int)
    requires 
        s.no_duplicates(),
        min <= max,
        forall |e: int| s.contains(e) ==> min <= e < max,
    ensures 
        s.len() <= max - min,
{
    let s_set = s.to_set();
    // s_set.len() == s.len() because s has no duplicates
    s.unique_seq_to_set();
    // because s_set only has values between min and max, it's a subset 
    // of the set containing all values between min and max
    assert(s_set.subset_of(set_int_range(min, max)));
    lemma_int_range(min, max);
    lemma_len_subset(s_set, set_int_range(min, max));
    assert(s.len() <= set_int_range(min, max).len());
}

// TODO: Do this more efficiently by just calling Vec::clone.
pub exec fn clone_pmcopy_vec<T: PmCopy>(v: &Vec<T>) -> (result: Vec<T>)
    ensures
        result@ == v@,
{
    let mut result = Vec::<T>::new();
    assert(v@.take(0int) =~= Seq::<T>::empty());
    for pos in 0..v.len()
        invariant
            result@ == v@.take(pos as int),
    {
        assert(v@.take(pos as int).push(v@[pos as int]) =~= v@.take(pos + 1));
        result.push(v[pos].clone_provable());
    }
    assert(v@.take(v@.len() as int) =~= v@);
    result
}

#[inline]
pub exec fn extend_vec_u8_from_slice(v: &mut Vec<u8>, s: &[u8])
    ensures
        v@ == old(v)@ + s@,
{
    v.extend_from_slice(s);
    assert(v@ =~= old(v)@ + s@);
}


pub proof fn lemma_set_to_seq_contains_iff_set_contains<A>(s: Set<A>, v: A)
    requires
        s.finite(),
    ensures
        s.contains(v) <==> s.to_seq().contains(v),
    decreases
        s.len(),
{
    if s.len() != 0 {
        let x = s.choose();
        let s2 = s.remove(x).to_seq();
        assert(s.to_seq() == Seq::<A>::empty().push(x) + s2);
        if v == x {
            assert(s.contains(v));
            assert(s.to_seq()[0] == v);
            assert(s.to_seq().contains(v));
        }
        else {
            lemma_set_to_seq_contains_iff_set_contains(s.remove(x), v);
            if s.contains(v) {
                assert(s.remove(x).contains(v));
                assert(s.remove(x).to_seq().contains(v));
                let i = choose|i: int| 0 <= i < s2.len() && s2[i] == v;
                assert(s.to_seq()[i + 1] == v);
                assert(s.to_seq().contains(v));
            }
        }
    }
}

pub proof fn lemma_set_to_seq_has_same_length_with_no_duplicates<A>(s: Set<A>)
    requires
        s.finite(),
    ensures
        s.to_seq().len() == s.len(),
        s.to_seq().no_duplicates(),
    decreases
        s.len(),
{
    let q = s.to_seq();
    if s.len() != 0 {
        let x = s.choose();
        lemma_set_to_seq_has_same_length_with_no_duplicates(s.remove(x));
        assert(!s.remove(x).to_seq().contains(x)) by {
            lemma_set_to_seq_contains_iff_set_contains(s.remove(x), x);
        }
    }
    q.unique_seq_to_set();
}

pub proof fn lemma_bijection_makes_sets_have_equal_size<A, B>(
    s1: Set<A>,
    s2: Set<B>,
    f: spec_fn(A) -> B,
    g: spec_fn(B) -> A,
)
    requires
        s1.finite(),
        forall|x: A| #[trigger] s1.contains(x) ==> s2.contains(f(x)) && x == g(f(x)),
        forall|y: B| #[trigger] s2.contains(y) ==> s1.contains(g(y)) && y == f(g(y)),
    ensures
        s2.finite(),
        s2.len() == s1.len(),
{
    // Convert set `s1` to a sequence and prove key properties of the
    // resulting `q1`:
    // * `q1` contains exactly the same values as `s1`.
    // * `q1` has the same length as `s1`.
    // * `q1` has no duplicates. 

    let q1 = s1.to_seq();
    assert forall|x: A| #[trigger] q1.contains(x) <==> s1.contains(x) by {
        lemma_set_to_seq_contains_iff_set_contains(s1, x);
    }
    assert(q1.len() == s1.len() && q1.no_duplicates()) by {
        lemma_set_to_seq_has_same_length_with_no_duplicates(s1);
    }

    // Convert sequence `q1` to a new sequence `q2` by applying the
    // transformation `f`.

    let q2 = Seq::<B>::new(q1.len(), |i: int| f(q1[i]));

    // Prove that `q2.to_set() == s2`. This also establishes that `s2`
    // is finite, from the ambient broadcast proof
    // `vstd::seq_lib::seq_to_set_is_finite`.

    assert(q2.to_set() =~= s2) by {
        assert forall|y: B| #[trigger] q2.to_set().contains(y) implies s2.contains(y) by {
            assert(q2.contains(y));
            let i = choose|i: int| 0 <= i < q2.len() && q2[i] == y;
            assert(y == f(q1[i]));
            assert(q1.contains(q1[i]));
            assert(s1.contains(q1[i]));
            assert(s2.contains(f(q1[i]))); // by bijectivity
        }
        assert forall|y: B| #[trigger] s2.contains(y) implies q2.to_set().contains(y) by {
            assert(s1.contains(g(y))); // by bijectivity
            let x = g(y);
            assert(q1.contains(x));
            let i = choose|i: int| 0 <= i < q1.len() && q1[i] == x;
            assert(q2[i] == f(x));
            assert(q2.to_set().contains(f(x)));
            assert(f(x) == y);
        }
    }

    // Now prove that `q2` has no duplicates.

    assert(q2.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < q2.len() && 0 <= j < q2.len() && i != j implies q2[i] != q2[j] by {
            assert(q2[i] == f(q1[i]) && q2[j] == f(q1[j]));
            assert(q1.contains(q1[i]) && q1.contains(q1[j]));
            assert(s1.contains(q1[i]) && s1.contains(q1[j]));
            let x1 = g(q2[i]);
            let x2 = g(q2[j]);
            assert(x1 == q1[i] && x2 == q1[j]);
        }
    }

    // Finally, prove that `q2` has the same length as `s2`. This is
    // enough because we know by construction of `q2` that it has the
    // same length as `q1` and we proved earlier that `q1` has the
    // same length as `s1`.

    assert(q2.len() == s2.len()) by {
        q2.unique_seq_to_set();
    }
}

}
