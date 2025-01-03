#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::nonlinear_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::kvimpl_t::*;
use super::kvspec_t::*;
use vstd::arithmetic::div_mod::{lemma_div_of0, lemma_div_plus_one, lemma_fundamental_div_mod_converse};
use vstd::arithmetic::mul::{lemma_mul_basics, lemma_mul_inequality, lemma_mul_is_distributive_add_other_way};

verus! {

#[repr(C)]
#[derive(PmCopy, Copy)]
#[verifier::ext_equal]
pub struct TableMetadata
{
    pub start: u64,
    pub end: u64,
    pub num_rows: u64,
    pub row_size: u64,
}

impl TableMetadata
{
    pub closed spec fn valid(self) -> bool
    {
        &&& 0 < self.row_size
        &&& opaque_mul(self.num_rows as int, self.row_size as int) <= self.end - self.start
    }

    pub closed spec fn row_index_to_addr(self, row_index: int) -> int
    {
        self.start + opaque_mul(row_index, self.row_size as int)
    }

    pub closed spec fn row_addr_to_index(self, addr: int) -> int
    {
        opaque_div(addr - self.start, self.row_size as int)
    }

    pub closed spec fn validate_row_addr(self, addr: int) -> bool
    {
        let row_index = self.row_addr_to_index(addr);
        &&& 0 <= row_index < self.num_rows
        &&& addr == self.start + opaque_mul(row_index, self.row_size as int)
    }

    pub exec fn new(start: u64, end: u64, num_rows: u64, row_size: u64) -> (result: Self)
        requires
            0 < row_size,
            opaque_mul(num_rows as int, row_size as int) <= end - start,
        ensures
            result == (Self{ start, end, num_rows, row_size }),
            result.valid()
    {
        Self{ start, end, num_rows, row_size }
    }
}

pub broadcast proof fn broadcast_validate_row_addr_effects(tm: TableMetadata, addr: int)
    requires
        tm.valid(),
        #[trigger] tm.validate_row_addr(addr),
    ensures
        tm.start <= addr,
        addr + tm.row_size <= tm.end,
{
    let row_index = tm.row_addr_to_index(addr);
    reveal(opaque_mul);
    lemma_mul_inequality(row_index + 1, tm.num_rows as int, tm.row_size as int);
    assert(addr + tm.row_size == tm.start + (row_index + 1) * tm.row_size) by {
        lemma_mul_is_distributive_add_other_way(tm.row_size as int, row_index as int, 1);
        lemma_mul_basics(tm.row_size as int);
    }
}

pub broadcast proof fn broadcast_validate_row_addr_nonoverlapping(tm: TableMetadata, addr1: int, addr2: int)
    requires
        tm.valid(),
        #[trigger] tm.validate_row_addr(addr1),
        #[trigger] tm.validate_row_addr(addr2),
    ensures
        addr1 != addr2 ==> {
            ||| addr1 + tm.row_size <= addr2
            ||| addr2 + tm.row_size <= addr1
        },
{
    reveal(opaque_mul);

    let row_index1 = tm.row_addr_to_index(addr1);
    let row_index2 = tm.row_addr_to_index(addr2);
    if row_index1 < row_index2 {
        lemma_mul_inequality(row_index1 + 1, row_index2 as int, tm.row_size as int);
    }
    if row_index1 > row_index2 {
        lemma_mul_inequality(row_index2 + 1, row_index1 as int, tm.row_size as int);
    }

    lemma_mul_is_distributive_add_other_way(tm.row_size as int, row_index1 as int, 1);
    lemma_mul_is_distributive_add_other_way(tm.row_size as int, row_index2 as int, 1);
}

pub proof fn lemma_start_is_valid_row(tm: TableMetadata)
    requires
        tm.num_rows > 0,
        tm.valid(),
    ensures
        tm.row_addr_to_index(tm.start as int) == 0,
        tm.num_rows > 0 ==> tm.validate_row_addr(tm.start as int),
{
    reveal(opaque_mul);
    reveal(opaque_div);
    lemma_div_of0(tm.row_size as int);
    assert(0int / tm.row_size as int == 0);
}

pub proof fn lemma_row_addr_successor_is_valid(tm: TableMetadata, addr: int)
    requires
        tm.num_rows > 0,
        tm.valid(),
        tm.validate_row_addr(addr),
    ensures 
        ({
            let row_index = tm.row_addr_to_index(addr);
            let new_addr = addr + tm.row_size;
            &&& tm.row_addr_to_index(new_addr) == row_index + 1
            &&& row_index + 1 < tm.num_rows ==> tm.validate_row_addr(new_addr)
        })
{
    reveal(opaque_mul);
    reveal(opaque_div);
    let new_addr = addr + tm.row_size;
    let row_index = tm.row_addr_to_index(addr);
    let new_row = (new_addr - tm.start) / (tm.row_size as int);
    lemma_mul_inequality(row_index + 1, tm.num_rows as int, tm.row_size as int);
    assert(new_row == row_index + 1) by {
        lemma_div_plus_one(addr - tm.start, tm.row_size as int);
    }
    assert(addr + tm.row_size == tm.start + (row_index + 1) * tm.row_size) by {
        lemma_mul_is_distributive_add_other_way(tm.row_size as int, row_index as int, 1);
        lemma_mul_basics(tm.row_size as int);
    }
}

pub broadcast proof fn lemma_row_index_to_addr_is_valid(tm: TableMetadata, row_index: int)
    requires
        tm.valid(),
        0 <= row_index < tm.num_rows,
    ensures
        tm.validate_row_addr(#[trigger] tm.row_index_to_addr(row_index))
{
    reveal(opaque_mul);
    reveal(opaque_div);
    let addr = tm.row_index_to_addr(row_index);
    assert(row_index == tm.row_addr_to_index(addr)) by {
       lemma_fundamental_div_mod_converse(addr - tm.start, tm.row_size as int, row_index, 0);
   }
}

pub broadcast group group_validate_row_addr {
    broadcast_validate_row_addr_effects,
    broadcast_validate_row_addr_nonoverlapping,
}

}
