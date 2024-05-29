use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;

pub unsafe trait PmSafe {}

// Numeric types and arrays are all always PmSafe.
// The PmSafe derive macro can derive PmSafe for any structure
// that contains only PmSafe types.
// Primitives that can have invalid values that would normally be prohibited
// by the compiler are *not* PmSafe because we cannot guarantee that the bytes
// being read have not been corrupted into an invalid value
// - bool: values other than 0/1 are UB
// - char: values that are not valid Unicode scalar values are UB
// TODO: check if char and f32/f64 are safe -- if any values lead to UB, not safe
unsafe impl PmSafe for u8 {}
unsafe impl PmSafe for u16 {}
unsafe impl PmSafe for u32 {}
unsafe impl PmSafe for u64 {}
unsafe impl PmSafe for u128 {}
unsafe impl PmSafe for usize {}
unsafe impl PmSafe for i8 {}
unsafe impl PmSafe for i16 {}
unsafe impl PmSafe for i32 {}
unsafe impl PmSafe for i64 {}
unsafe impl PmSafe for i128 {}
unsafe impl PmSafe for isize {}
// unsafe impl PmSafe for f32 {} // are these safe?
// unsafe impl PmSafe for f64 {}
unsafe impl<T: PmSafe, const N: usize> PmSafe for [T; N] {}


verus! {
    #[verifier::external_trait_specification]
    pub trait ExPmSafe {
        type ExternalTraitSpecificationFor: PmSafe;
    }
}