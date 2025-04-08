// This file defines the `TableMetadata` struct and its associated methods and proofs.
// It provides functionality for operating on tables in persistent memory where
// rows are consecutive and identically-sized. It hides all the nonlinear arithmetic
// (multiplication, division, and modulo by the row size) internally, providing an
// abstraction that doesn't require reasoning about such arithmetic. For instance,
// it provides a broadcast lemma saying that if two valid row addresses are unequal,
// then their rows don't overlap.

#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::util_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_div_of0, lemma_div_plus_one, lemma_fundamental_div_mod_converse,
};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_inequality, lemma_mul_is_distributive_add_other_way,
};

verus! {

// This struct represents metadata for a table in persistent memory, including the start and end
// addresses, number of rows, and size of each row.
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
    // Indicates whether the table metadata is valid. Note that it allows for
    // some unused space at the end of the table, perhaps for use in padding.
    pub closed spec fn valid(self) -> bool
    {
        &&& 0 < self.row_size
        &&& self.num_rows as int * self.row_size <= self.end - self.start
    }

    // Computes the address of a row given its index, based on the table metadata.
    pub closed spec fn spec_row_index_to_addr(self, row_index: int) -> u64
    {
        (self.start + row_index * self.row_size) as u64
    }

    // Computes the address of a row at runtime, given its index.
    // Hides the nonlinear arithmetic, providing a postcondition merely
    // stating that it's equivalent to the corresponding spec function.
    pub exec fn row_index_to_addr(self, row_index: u64) -> (out: u64)
        requires
            self.valid(),
            0 <= row_index < self.num_rows,
        ensures
            out == self.spec_row_index_to_addr(row_index as int),
            self.validate_row_addr(out),
    {
        proof { lemma_row_index_to_addr_is_valid(self, row_index as int); }
        self.start + row_index * self.row_size
    }

    // Computes the index of a row given its address, based on the table metadata.
    pub closed spec fn row_addr_to_index(self, addr: u64) -> int
    {
        (addr - self.start) / (self.row_size as int)
    }

    // Indicates whether a given address corresponds to a valid row in the table.
    pub closed spec fn validate_row_addr(self, addr: u64) -> bool
    {
        let row_index = self.row_addr_to_index(addr);
        &&& 0 <= row_index < self.num_rows
        &&& addr == self.start + row_index * self.row_size
    }

    // Creates a new `TableMetadata` instance with the specified parameters.
    pub exec fn new(start: u64, end: u64, num_rows: u64, row_size: u64) -> (result: Self)
        requires
            0 < row_size,
            num_rows * row_size <= end - start,
        ensures
            result == (Self{ start, end, num_rows, row_size }),
            result.valid()
    {
        Self{ start, end, num_rows, row_size }
    }

    // Proves that the start address corresponds to a valid row in the table.
    pub proof fn lemma_start_is_valid_row(self)
        requires
            self.valid(),
        ensures
            self.row_addr_to_index(self.start) == 0,
            self.num_rows > 0 ==> self.validate_row_addr(self.start),
    {
        lemma_div_of0(self.row_size as int);
        assert(0int / self.row_size as int == 0);
    }

    // Proves that the successor of a valid row address is also valid, as long as it's
    // not past the end of the table.
    pub proof fn lemma_row_addr_successor_is_valid(self, addr: u64)
        requires
            self.valid(),
            self.validate_row_addr(addr),
            addr + self.row_size <= self.end,
        ensures
            ({
                let row_index = self.row_addr_to_index(addr);
                let new_addr = (addr + self.row_size) as u64;
                &&& self.row_addr_to_index(new_addr) == row_index + 1
                &&& row_index + 1 <= self.num_rows
                &&& row_index + 1 < self.num_rows ==> self.validate_row_addr(new_addr)
            })
    {
        let new_addr = addr + self.row_size;
        let row_index = self.row_addr_to_index(addr);
        let new_row = (new_addr - self.start) / (self.row_size as int);
        lemma_mul_inequality(row_index + 1, self.num_rows as int, self.row_size as int);
        assert(new_row == row_index + 1) by {
            lemma_div_plus_one(addr - self.start, self.row_size as int);
        }
        assert(addr + self.row_size == self.start + (row_index + 1) * self.row_size) by {
            lemma_mul_is_distributive_add_other_way(self.row_size as int, row_index as int, 1);
            lemma_mul_basics(self.row_size as int);
        }
    }

    // Proves that `row_addr_to_index` and `row_index_to_addr` are inverses
    // of each other, when applied in either order.
    pub proof fn lemma_index_addr_inverse(self)
        requires
            self.valid(),
        ensures
            forall |addr: u64| #[trigger] self.validate_row_addr(addr) ==> {
                let row = self.row_addr_to_index(addr);
                addr == self.spec_row_index_to_addr(row)
            },
            forall |i: int| 0 <= i < self.num_rows ==> {
                let addr = #[trigger] self.spec_row_index_to_addr(i);
                i == self.row_addr_to_index(addr)
            },
    {
        assert forall |i: int| 0 <= i < self.num_rows implies {
            let addr = #[trigger] self.spec_row_index_to_addr(i);
            i == self.row_addr_to_index(addr)
        } by { lemma_row_index_to_addr_is_valid(self, i); }
    }

    // Proves that the set of valid row addresses has length equal to the number
    // of rows in the table. Also proves that that set is finite, so the length
    // is a meaningful quantity.
    pub proof fn lemma_valid_row_set_len(self)
        requires
            self.valid(),
        ensures
            ({
                let valid_row_addrs = Set::<u64>::new(|row_addr: u64| self.validate_row_addr(row_addr));
                &&& valid_row_addrs.len() == self.num_rows
                &&& valid_row_addrs.finite()
            }),
    {
        // The proof is in three parts.

        let valid_row_addrs = Set::<u64>::new(|row_addr: u64| self.validate_row_addr(row_addr));
        let rows: Seq<u64> = Seq::new(self.num_rows as nat, |row_index: int| self.spec_row_index_to_addr(row_index));

        // First, we prove that the sequence containing all row addresses in order has no duplicates.
        assert(rows.no_duplicates()) by {
            assert forall|i, j| (0 <= i < rows.len() && 0 <= j < rows.len() && i != j) implies rows[i] != rows[j] by {
                lemma_row_index_to_addr_is_valid(self, i);
                lemma_row_index_to_addr_is_valid(self, j);
            }
        }

        // Second, we prove that if you convert that sequence to a set, you get the set of valid row addresses.
        assert(rows.to_set() =~= valid_row_addrs) by {
            assert forall|row_addr: u64| #[trigger] rows.to_set().contains(row_addr)
                       implies valid_row_addrs.contains(row_addr) by {
                let row_index = choose|row_index: int| 0 <= row_index < rows.len() && rows[row_index] == row_addr;
                lemma_row_index_to_addr_is_valid(self, row_index);
            }
            assert forall|row_addr: u64| #[trigger] valid_row_addrs.contains(row_addr)
                       implies rows.to_set().contains(row_addr) by {
                let row_index = self.row_addr_to_index(row_addr);
                assert(0 <= row_index < rows.len());
                assert(rows[row_index] == row_addr);
            }
        }

        // Finally, we use `unique_seq_to_set`, a library function that proves that the length
        // of a set derived from a sequence with no duplicates is equal to the length of that sequence.
        rows.unique_seq_to_set();
    }
}

// Proves, in a way that can be used by broadcast, various facts about a given valid
// row address. Specifically, that it's within the bounds of the table, and that
// converting to a row index gives a number in [0, num_rows). The trigger for
// this broadcast is `tm.validate_row_addr(addr)`.
pub broadcast proof fn broadcast_validate_row_addr_effects(tm: TableMetadata, addr: u64)
    requires
        tm.valid(),
        #[trigger] tm.validate_row_addr(addr),
    ensures
        tm.start <= addr,
        addr + tm.row_size <= tm.end,
        0 <= tm.row_addr_to_index(addr) < tm.num_rows,
{
    let row_index = tm.row_addr_to_index(addr);
    lemma_mul_inequality(row_index + 1, tm.num_rows as int, tm.row_size as int);
    assert(addr + tm.row_size == tm.start + (row_index + 1) * tm.row_size) by {
        lemma_mul_is_distributive_add_other_way(tm.row_size as int, row_index as int, 1);
        lemma_mul_basics(tm.row_size as int);
    }
}

// Proves, in a way that can be used by broadcast, that two valid but unequal row
// addresses don't overlap in memory, and have different row indices. The trigger
// is two parts: `tm.validate_row_addr(addr1)` and `tm.validate_row_addr(addr2)`.
pub broadcast proof fn broadcast_validate_row_addr_nonoverlapping(tm: TableMetadata, addr1: u64, addr2: u64)
    requires
        tm.valid(),
        #[trigger] tm.validate_row_addr(addr1),
        #[trigger] tm.validate_row_addr(addr2),
    ensures
        addr1 != addr2 ==> {
            ||| addr1 + tm.row_size <= addr2
            ||| addr2 + tm.row_size <= addr1
        },
        addr1 != addr2 ==> tm.row_addr_to_index(addr1) != tm.row_addr_to_index(addr2),
{
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

// Proves, in a way that can be used by broadcast, that converting a row index to an address
// produces a valid address, and that converting that address back to a row index gives the original
// row index. The trigger is `tm.spec_row_index_to_addr(row_index)`.
pub broadcast proof fn lemma_row_index_to_addr_is_valid(tm: TableMetadata, row_index: int)
    requires
        tm.valid(),
        0 <= row_index < tm.num_rows,
    ensures
        tm.validate_row_addr(#[trigger] tm.spec_row_index_to_addr(row_index)),
        tm.row_addr_to_index(tm.spec_row_index_to_addr(row_index)) == row_index,
{
    let addr = tm.spec_row_index_to_addr(row_index);
    assert(row_index * tm.row_size <= tm.num_rows * tm.row_size) by {
        lemma_mul_inequality(row_index, tm.num_rows as int, tm.row_size as int);
    }
    assert(row_index == tm.row_addr_to_index(addr)) by {
       lemma_fundamental_div_mod_converse(addr - tm.start, tm.row_size as int, row_index, 0);
    }
}

// Provides a useful collection of broadcast lemmas for reasoning about valid rows.
pub broadcast group group_validate_row_addr {
    broadcast_validate_row_addr_effects,
    broadcast_validate_row_addr_nonoverlapping,
}

}
