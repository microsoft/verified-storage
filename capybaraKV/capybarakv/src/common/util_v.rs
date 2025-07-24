// This file contains miscellaneous utility functions.
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;

verus! {

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

// This lemma proves that if a map is injective, then inverting it twice produces
// the original map.
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

// Proves that if a map `map` is injective, then `map.invert()` maps
// its values to its keys.
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

// This executable function clones a vector of objects of type `T`
// when `T` implements the `PmCopy` trait.
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
        decreases
            v.len() - pos
    {
        assert(v@.take(pos as int).push(v@[pos as int]) =~= v@.take(pos + 1));
        result.push(v[pos].clone_provable());
    }
    assert(v@.take(v@.len() as int) =~= v@);
    result
}

// This executable function extends a `Vec<u8>` with the contents of
// a slice.
#[inline]
pub exec fn extend_vec_u8_from_slice(v: &mut Vec<u8>, s: &[u8])
    ensures
        v@ == old(v)@ + s@,
{
    v.extend_from_slice(s);
    assert(v@ =~= old(v)@ + s@);
}


// Proves that, given that `s` is finite, it contains `v` if and only if
// `s.to_seq()` contains `v`.
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

// Proves that, given that `s` is finite, `s.to_seq()` has the same length as `s`
// and has no duplicates.
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

// Prove that if there exists a bijection between two sets `s1` and `s2`,
// where `s1` is known to be finite, then `s2` is also finite and
// has the same length as `s1`. The bijection takes the form of two
// functions `f` and `g`, where `f` maps elements from `s1` to `s2`
// and `g` maps elements from `s2` to `s1`.
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

// Proves that `s.fold_left(c, g)` can be expressed as a `fold_left`
// of `s.map_values(f)`. For this, we require a fold function `h` that
// inverts the effect of `f`.
pub proof fn lemma_fold_equivalent_to_map_fold<A, B, C>(
    c: C,
    s: Seq<A>,
    f: spec_fn(A) -> B,
    g: spec_fn(C, A) -> C,
    h: spec_fn(C, B) -> C,
)
    requires
        forall|k: C, a: A| s.contains(a) ==> #[trigger] g(k, a) == h(k, f(a)),
    ensures
        s.fold_left(c, g) == s.map_values(f).fold_left(c, h),
    decreases
        s.len(),
{
    if s.len() != 0 {
        lemma_fold_equivalent_to_map_fold(c, s.drop_last(), f, g, h);
        assert(s.drop_last().map_values(f) =~= s.map_values(f).drop_last());
    }
}

// Proves that if `s.filter(pred)` contains `x`, then `s` contains `x` and `pred(x)` is true.
pub proof fn lemma_if_filter_contains_then_original_contains<A>(s: Seq<A>, pred: spec_fn(A) -> bool, x: A)
    ensures
        s.filter(pred).contains(x) ==> s.contains(x) && pred(x),
    decreases
        s.len(),
{
    reveal(Seq::filter);
    if s.len() != 0 {
        lemma_if_filter_contains_then_original_contains(s.drop_last(), pred, x);
    }
}

// Proves that if `s` has no duplicates, then `s.filter(pred)` also has no duplicates.
pub proof fn lemma_filter_preserves_no_duplicates<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    requires
        s.no_duplicates(),
    ensures
        s.filter(pred).no_duplicates(),
    decreases
        s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        lemma_filter_preserves_no_duplicates(s.drop_last(), pred);
        assert(s.drop_last().filter(pred).no_duplicates());
        if s.drop_last().filter(pred).contains(s.last()) {
            lemma_if_filter_contains_then_original_contains(s.drop_last(), pred, s.last());
            assert(s.drop_last().contains(s.last()));
            let i = choose|i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == s.last();
            let j = s.len() - 1;
            assert(0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] == s[j]);
            assert(false);
        }
    }
}

// Indicates whether the given function `f` used for `fold_left` is commutative.
pub open spec fn commutative_foldl<A, B>(f: spec_fn(B, A) -> B) -> bool {
    forall|x: A, y: A, v: B| #[trigger] f(f(v, x), y) == f(f(v, y), x)
}

// Converts a `fold_left` function to a `fold_right` function.
pub open spec fn convert_foldl_to_foldr<A, B>(f: spec_fn(B, A) -> B) -> (spec_fn(A, B) -> B)
{
    |a: A, b: B| f(b, a)
}

// Proves that if `f` is a commutative `fold_left` function, then the result of
// folding left using `f` is equal to the result of folding right using
// `convert_foldl_to_foldr(f)`. Furthermore, `convert_foldl_to_foldr(f)` is
// a commutative `fold_right` function.
pub proof fn lemma_commutative_foldl_equivalent_to_corresponding_foldr<A, B>(
    s: Seq<A>,
    b: B,
    f: spec_fn(B, A) -> B
)
    requires
        commutative_foldl(f),
    ensures
        commutative_foldr(convert_foldl_to_foldr(f)),
        s.fold_left(b, f) == s.fold_right(convert_foldl_to_foldr(f), b),
    decreases
        s.len(),
{
    if s.len() > 0 {
        let fr = convert_foldl_to_foldr(f);
        lemma_commutative_foldl_equivalent_to_corresponding_foldr(s.drop_last(), b, f);
        s.drop_last().lemma_fold_right_commute_one(s.last(), convert_foldl_to_foldr(f), b);
    }
}

// Proves that if two sequences `s1` and `s2` have no duplicates and map to the same set,
// then they're permutations of each other.
pub proof fn lemma_two_seqs_with_no_duplicates_and_same_to_set_are_permutations<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.no_duplicates(),
        s2.no_duplicates(),
        s1.to_set() == s2.to_set(),
    ensures
        s1.to_multiset() == s2.to_multiset(),
{
    s1.lemma_multiset_has_no_duplicates();
    s2.lemma_multiset_has_no_duplicates();
    let m1 = s1.to_multiset();
    let m2 = s2.to_multiset();
    
    broadcast use to_multiset_contains;
    assert forall|x| m1.contains(x) implies m2.contains(x) && m2.count(x) == m1.count(x) by {
        assert(s1.contains(x));
        assert(s1.to_set().contains(x));
        assert(s2.to_set().contains(x));
        assert(s2.contains(x));
    }
    assert forall|x| m2.contains(x) implies m1.contains(x) && m2.count(x) == m1.count(x) by {
        assert(s2.contains(x));
        assert(s2.to_set().contains(x));
        assert(s1.to_set().contains(x));
        assert(s1.contains(x));
    }
    assert(m1 =~= m2);
}

}
