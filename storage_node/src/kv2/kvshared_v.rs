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

    pub closed spec fn which_row_to_row_addr(self, which_row: int) -> int
    {
        self.start + opaque_mul(which_row, self.row_size as int)
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

pub closed spec fn row_addr_to_which_row(addr: int, tm: TableMetadata) -> int
{
    opaque_div(addr - tm.start, tm.row_size as int)
}

pub closed spec fn is_valid_row_addr(addr: int, tm: TableMetadata) -> bool
{
    let which_row = row_addr_to_which_row(addr, tm);
    &&& 0 <= which_row < tm.num_rows
    &&& addr == tm.start + opaque_mul(which_row, tm.row_size as int)
}

pub broadcast proof fn broadcast_is_valid_row_addr_effects(addr: int, tm: TableMetadata)
    requires
        tm.valid(),
        #[trigger] is_valid_row_addr(addr, tm),
    ensures
        tm.start <= addr,
        addr + tm.row_size <= tm.end,
{
    let which_row = row_addr_to_which_row(addr, tm);
    reveal(opaque_mul);
    lemma_mul_inequality(which_row + 1, tm.num_rows as int, tm.row_size as int);
    assert(addr + tm.row_size == tm.start + (which_row + 1) * tm.row_size) by {
        lemma_mul_is_distributive_add_other_way(tm.row_size as int, which_row as int, 1);
        lemma_mul_basics(tm.row_size as int);
    }
}

pub broadcast proof fn broadcast_is_valid_row_addr_nonoverlapping(addr1: int, addr2: int, tm: TableMetadata)
    requires
        tm.valid(),
        #[trigger] is_valid_row_addr(addr1, tm),
        #[trigger] is_valid_row_addr(addr2, tm),
    ensures
        addr1 != addr2 ==> {
            ||| addr1 + tm.row_size <= addr2
            ||| addr2 + tm.row_size <= addr1
        },
{
    reveal(opaque_mul);

    let which_row1 = row_addr_to_which_row(addr1, tm);
    let which_row2 = row_addr_to_which_row(addr2, tm);
    if which_row1 < which_row2 {
        lemma_mul_inequality(which_row1 + 1, which_row2 as int, tm.row_size as int);
    }
    if which_row1 > which_row2 {
        lemma_mul_inequality(which_row2 + 1, which_row1 as int, tm.row_size as int);
    }

    lemma_mul_is_distributive_add_other_way(tm.row_size as int, which_row1 as int, 1);
    lemma_mul_is_distributive_add_other_way(tm.row_size as int, which_row2 as int, 1);
}

pub proof fn lemma_start_is_valid_row(tm: TableMetadata)
    requires
        tm.num_rows > 0,
        tm.valid(),
    ensures
        row_addr_to_which_row(tm.start as int, tm) == 0,
        tm.num_rows > 0 ==> is_valid_row_addr(tm.start as int, tm),
{
    reveal(opaque_mul);
    reveal(opaque_div);
    lemma_div_of0(tm.row_size as int);
    assert(0int / tm.row_size as int == 0);
}

pub proof fn lemma_row_addr_successor_is_valid(addr: int, tm: TableMetadata)
    requires
        tm.num_rows > 0,
        tm.valid(),
        is_valid_row_addr(addr, tm),
    ensures 
        ({
            let which_row = row_addr_to_which_row(addr, tm);
            let new_addr = addr + tm.row_size;
            &&& row_addr_to_which_row(new_addr, tm) == which_row + 1
            &&& which_row + 1 < tm.num_rows ==> is_valid_row_addr(new_addr, tm)
        })
{
    reveal(opaque_mul);
    reveal(opaque_div);
    let new_addr = addr + tm.row_size;
    let which_row = row_addr_to_which_row(addr, tm);
    let new_row = (new_addr - tm.start) / (tm.row_size as int);
    lemma_mul_inequality(which_row + 1, tm.num_rows as int, tm.row_size as int);
    assert(new_row == which_row + 1) by {
        lemma_div_plus_one(addr - tm.start, tm.row_size as int);
    }
    assert(addr + tm.row_size == tm.start + (which_row + 1) * tm.row_size) by {
        lemma_mul_is_distributive_add_other_way(tm.row_size as int, which_row as int, 1);
        lemma_mul_basics(tm.row_size as int);
    }
}

pub proof fn lemma_which_row_to_row_addr_is_valid(which_row: int, tm: TableMetadata)
    requires
        tm.valid(),
        0 <= which_row < tm.num_rows,
    ensures
        is_valid_row_addr(tm.which_row_to_row_addr(which_row), tm)
{
    reveal(opaque_mul);
    reveal(opaque_div);
    let addr = tm.which_row_to_row_addr(which_row);
    assert(which_row == row_addr_to_which_row(addr, tm)) by {
       lemma_fundamental_div_mod_converse(addr - tm.start, tm.row_size as int, which_row, 0);
   }
}

pub broadcast group group_is_valid_row_addr {
    broadcast_is_valid_row_addr_effects,
    broadcast_is_valid_row_addr_nonoverlapping,
}

}
