use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::{pmcopy_t::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};

verus! {

#[verifier::opaque]
pub open spec fn opaque_subrange<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
{
    s.subrange(i, j)
}

pub open spec fn opaque_section<T>(s: Seq<T>, i: int, len: nat) -> Seq<T>
{
    opaque_subrange(s, i, i + len)
}

#[verifier::opaque]
pub open spec fn opaque_aligned(addr: int, alignment: int) -> bool
{
    addr % alignment == 0
}

#[verifier::opaque]
pub open spec fn opaque_update_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>) -> Seq<u8>
{
    update_bytes(s, addr, bytes)
}

pub open spec fn recover_object<T>(s: Seq<u8>, start: int) -> Option<T>
    where
        T: PmCopy
{
    if 0 <= start && start + T::spec_size_of() + u64::spec_size_of() <= s.len() {
        let object_bytes = opaque_section(s, start, T::spec_size_of());
        let crc_bytes = opaque_section(s, T::spec_size_of() as int, u64::spec_size_of());
        if crc_bytes == spec_crc_bytes(object_bytes) && T::bytes_parseable(object_bytes) {
            Some(T::spec_from_bytes(object_bytes))
        }
        else {
            None
        }
    }
    else {
        None
    }
}

pub open spec fn recover_cdb(bytes: Seq<u8>, addr: int) -> Option<bool>
{
    match recover_object::<u64>(bytes, addr) {
        Some(cdb) => if cdb == CDB_FALSE { Some(false) } else if cdb == CDB_TRUE { Some(true) } else { None },
        None => None,
    }
}

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
}
