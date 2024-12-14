use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;

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

pub open spec fn opaque_match_except_in_range(s1: Seq<u8>, s2: Seq<u8>, start: int, end: int) -> bool
{
    &&& s1.len() == s2.len()
    &&& 0 <= start <= end <= s1.len()
    &&& opaque_subrange(s1, 0, start) == opaque_subrange(s2, 0, start)
    &&& opaque_subrange(s1, end, s1.len() as int) == opaque_subrange(s2, end, s2.len() as int)
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

pub closed spec fn space_needed_for_alignment(addr: int, alignment: int) -> int
{
    let remainder = addr % alignment;
    if remainder == 0 {
        0
    }
    else {
        alignment - remainder
    }
}

pub open spec fn round_up_to_alignment(addr: int, alignment: int) -> int
{
    addr + space_needed_for_alignment(addr, alignment)
}

pub proof fn lemma_space_needed_for_alignment_works(addr: int, alignment: int)
    requires
        0 < alignment,
    ensures
        space_needed_for_alignment(addr, alignment) >= 0,
        opaque_aligned(addr + space_needed_for_alignment(addr, alignment), alignment)
{
    reveal(opaque_aligned);
    let remainder = addr % alignment;
    if remainder != 0 {
        assert(addr == alignment * (addr / alignment) + (addr % alignment)) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(addr, alignment);
        }
        assert(addr + alignment - remainder == alignment * (addr / alignment) + alignment);
        assert((addr + alignment - remainder) % alignment == alignment % alignment) by {
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(addr / alignment, alignment, alignment);
        }
    }
}

pub exec fn increment_addr(current_addr: u64, increment_amount: u64, size: u64) -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
    ensures
        ({
            let new_addr = current_addr + increment_amount;
            match result {
                Some(v) => new_addr <= size && v == new_addr,
                None => new_addr > size,
            }
        })
{
    if current_addr > u64::MAX - increment_amount {
        None
    }
    else {
        let new_addr = current_addr + increment_amount;
        if new_addr <= size {
            Some(new_addr)
        }
        else {
            None
        }
    }
}

pub exec fn align_addr(current_addr: u64, alignment: u64, size: u64) -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
        0 < alignment,
    ensures
        ({
            let new_addr = round_up_to_alignment(current_addr as int, alignment as int);
            match result {
                Some(v) => {
                    &&& current_addr <= new_addr
                    &&& new_addr <= size
                    &&& v == new_addr
                    &&& opaque_aligned(new_addr as int, alignment as int)
                },
                None => new_addr > size,
            }
        })
{
    let remainder = current_addr % alignment;
    let increment_amount = if remainder == 0 {
        0
    }
    else {
        alignment - remainder
    };
    proof {
        lemma_space_needed_for_alignment_works(current_addr as int, alignment as int);
    }
    increment_addr(current_addr, increment_amount, size)
}

pub exec fn increment_and_align_addr(current_addr: u64, increment_amount: u64, alignment: u64, size: u64)
                                     -> (result: Option<u64>)
    requires
        0 <= current_addr <= size,
        0 < alignment,
    ensures
        ({
            let new_addr = round_up_to_alignment(current_addr + increment_amount, alignment as int);
            match result {
                Some(v) => {
                    &&& current_addr + increment_amount <= new_addr
                    &&& new_addr <= size
                    &&& v == new_addr
                    &&& opaque_aligned(new_addr as int, alignment as int)
                },
                None => new_addr > size,
            }
        })
{
    let new_addr = increment_addr(current_addr, increment_amount, size)?;
    align_addr(new_addr, alignment, size)
}

pub proof fn lemma_can_result_from_partial_write_effect_on_opaque(
    s2: Seq<u8>,
    s1: Seq<u8>,
    write_addr: int,
    bytes: Seq<u8>
)
    requires
        can_result_from_partial_write(s2, s1, write_addr, bytes),
        0 <= write_addr,
        write_addr + bytes.len() <= s1.len(),
    ensures
        opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len()),
{
    lemma_can_result_from_partial_write_effect(s2, s1, write_addr, bytes);
    reveal(opaque_subrange);
    assert(opaque_subrange(s1, 0, write_addr) =~= opaque_subrange(s2, 0, write_addr));
    assert(opaque_subrange(s1, write_addr + bytes.len(), s1.len() as int) =~=
           opaque_subrange(s2, write_addr + bytes.len(), s2.len() as int));
}

pub proof fn lemma_auto_can_result_from_partial_write_effect_on_opaque()
    ensures
        forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
            &&& #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes)
            &&& 0 <= write_addr
            &&& write_addr + bytes.len() <= s1.len()
        } ==> opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len())
{
    assert forall|s2: Seq<u8>, s1: Seq<u8>, write_addr: int, bytes: Seq<u8>| {
               &&& #[trigger] can_result_from_partial_write(s2, s1, write_addr, bytes)
               &&& 0 <= write_addr
               &&& write_addr + bytes.len() <= s1.len()
    } implies opaque_match_except_in_range(s1, s2, write_addr, write_addr + bytes.len()) by {
        lemma_can_result_from_partial_write_effect_on_opaque(s2, s1, write_addr, bytes);
    }
}

}
