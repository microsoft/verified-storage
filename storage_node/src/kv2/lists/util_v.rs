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
use vstd::std_specs::hash::*;

verus! {

pub(super) proof fn lemma_writing_next_and_crc_together_enables_recovery(
    s1: Seq<u8>,
    s2: Seq<u8>,
    next: u64,
    next_addr: int,
    bytes_written: Seq<u8>
)
    requires
        0 <= next_addr,
        next_addr + bytes_written.len() <= s1.len(),
        bytes_written.len() == u64::spec_size_of() + u64::spec_size_of(),
        s2 == update_bytes(s1, next_addr, bytes_written),
        bytes_written == next.spec_to_bytes() + spec_crc_bytes(next.spec_to_bytes()),
    ensures
        recover_object::<u64>(s2, next_addr, next_addr + u64::spec_size_of()) == Some(next),
{
    broadcast use group_update_bytes_effect;
    broadcast use pmcopy_axioms;

    let next_crc = spec_crc_bytes(next.spec_to_bytes());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr as int, next_addr + u64::spec_size_of());
    lemma_subrange_subrange(s2,
                            next_addr as int, next_addr + u64::spec_size_of() + u64::spec_size_of(),
                            next_addr + u64::spec_size_of(),
                            next_addr + u64::spec_size_of() + u64::spec_size_of());
    assert(bytes_written.subrange(0, u64::spec_size_of() as int) =~= next.spec_to_bytes());
    assert(bytes_written.subrange(u64::spec_size_of() as int, (u64::spec_size_of() + u64::spec_size_of()) as int)
           =~= next_crc);
    assert(recover_object::<u64>(s2, next_addr, next_addr + u64::spec_size_of()) =~= Some(next));
}

}

