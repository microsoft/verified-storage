use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;

pub unsafe trait PmSafe {
}

// Numeric types, bools, chars, and arrays are all always PmSafe.
// The PmSafe derive macro can derive PmSafe for any structure
// that contains only PmSafe types.
// TODO: declarative macro for these?
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
unsafe impl PmSafe for f32 {}
unsafe impl PmSafe for f64 {}
unsafe impl PmSafe for bool {}
unsafe impl PmSafe for char {}
unsafe impl<T: PmSafe, const N: usize> PmSafe for [T; N] {}


verus! {
    #[verifier::external_trait_specification]
    pub trait ExPmSafe {
        type ExternalTraitSpecificationFor: PmSafe;
    }
}