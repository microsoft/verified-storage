use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmemspec_t::*;

verus! {
    // This lemma proves that an index that is less than num_keys (i.e., within bounds of the table) 
    // represents a valid table entry that we can read and parse.
    pub proof fn lemma_valid_entry_index(index: nat, num_keys: nat, size: nat)
        requires
            index + 1 <= num_keys
        ensures 
            (index + 1) * size == index * size + size <= num_keys * size
    {
        vstd::arithmetic::mul::lemma_mul_inequality(index + 1 as int, num_keys as int, size as int);
        vstd::arithmetic::mul::lemma_mul_basics(size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int,
                                                                        index as int, 1);
    }

    // This lemma proves that a subrange of a subrange is equal to just obtaining the final subrange using its 
    // absolute start index. This is obvious and requires no body, but having a dedicated lemma helps
    // Z3 establish the equality
    pub proof fn lemma_subrange_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
        requires 
            start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
        ensures 
            ({
                let start_offset = start2 - start1;
                extract_bytes(extract_bytes(mem, start1, len1), start_offset as nat, len2) =~= extract_bytes(mem, start2, len2)
            })
    {}
}