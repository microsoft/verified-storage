use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmemspec_t::*;

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
}