#![cfg_attr(verus_keep_ghost, verus::trusted)]
// This file defines the Hamming distance between two byte sequences
// as the count of the number of bits that differ between the two. We
// use this for modeling patterns of expected bit corruption.

use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::*;

verus! {
    // Computes the sum of the given sequence of natural numbers
    pub open spec fn sum(l: Seq<nat>) -> nat {
        l.fold_right(|i, s: nat| { s+i as nat }, 0)
    }

    // Computes the population count of a byte, i.e., the number of
    // its bits that are 1.
    #[verifier::inline]
    pub open spec fn _popcnt_byte(a: u8) -> nat {
        let p0 = 1u8 & (a >> 0u8);
        let p1 = 1u8 & (a >> 1u8);
        let p2 = 1u8 & (a >> 2u8);
        let p3 = 1u8 & (a >> 3u8);
        let p4 = 1u8 & (a >> 4u8);
        let p5 = 1u8 & (a >> 5u8);
        let p6 = 1u8 & (a >> 6u8);
        let p7 = 1u8 & (a >> 7u8);
        let sum = add(p0, add(p1, add(p2, add(p3, add(p4, add(p5, add(p6, p7)))))));
        sum as nat
    }

    // Computes the population count of a byte, i.e., the number of
    // its bits that are 1.
    pub open spec fn popcnt_byte(a: u8) -> nat {
        _popcnt_byte(a)
    }

    // Given a byte sequence, computes a population-count sequence
    // where each element of the resulting sequence is the population
    // count of the corresponding byte in the given sequence.
    pub open spec fn popcnt_seq(l: Seq<u8>) -> Seq<nat> {
        l.map_values(|v: u8| popcnt_byte(v))
    }

    // Computes the population count of a byte sequence, i.e., the
    // number of its bits that are 1, ranging across all bits of all
    // its byte
    pub open spec fn popcnt(l: Seq<u8>) -> nat {
        sum(popcnt_seq(l))
    }

    // Bitwise XOR and AND for sequences
    pub open spec fn xor(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
        a.zip_with(b).map_values(|v: (u8, u8)| v.0 ^ v.1)
    }

    // Definition of Hamming distance
    pub open spec fn hamming(a: Seq<u8>, b: Seq<u8>) -> nat {
        popcnt(xor(a, b))
    }
}
