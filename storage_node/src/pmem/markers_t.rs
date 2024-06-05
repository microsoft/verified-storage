use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;
use deps_hack::PmSafe;

pub unsafe trait PmSafe {}

// Numeric types and arrays are all always PmSafe.
// The PmSafe derive macro can derive PmSafe for any structure
// that contains only PmSafe types.
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
unsafe impl<T: PmSafe, const N: usize> PmSafe for [T; N] {}

// These types are safe, even though reading invalid bytes and casting them to these types 
// causes UB, because a reader must prove that the bytes they read are a serialization of a 
// valid instance of a type before casting it to that type. If the last bytes written to this 
// location were a valid instance of the target type, and we prove that corruption did not 
// occur, then we know that the bytes we read are also valid.
unsafe impl PmSafe for bool {}
unsafe impl PmSafe for char {}
unsafe impl PmSafe for f32 {} 
unsafe impl PmSafe for f64 {}

// #[const_trait]
// pub trait PmSized {
//     // #[verifier::external]
//     const SIZE_CHECK: usize;

//     fn size_of() -> usize;
//         // requires
//         //     Self::spec_size_of() <= usize::MAX as nat,
//         // ensures 
//         //     out as int == Self::spec_size_of();
//     // spec fn spec_size_of() -> int;

//     fn align_of() -> usize;
//         // ensures 
//         //     out > 0,
//         //     out as int == Self::spec_align_of();
//     // spec fn spec_align_of() -> int;
// }

verus! {
    #[verifier::external_trait_specification]
    pub trait ExPmSafe {
        type ExternalTraitSpecificationFor: PmSafe;
    }

    #[verifier::external_trait_specification]
    pub trait ExPmSized {
        type ExternalTraitSpecificationFor: PmSized;

        fn size_of() -> usize;
        fn align_of() -> usize;
    }
}

pub trait PmSized {
    fn size_of() -> usize;
    fn align_of() -> usize;
}

// impl PmSized for u64 {
//     fn size_of() -> usize { Self::SIZE }
//     fn align_of() -> usize { Self::ALIGN }
// }

// #[const_trait]
pub trait ConstPmSized {
    const SIZE: usize;
    const ALIGN: usize;
    // const SIZE_CHECK: usize;
}

// impl ConstPmSized for u64 {
//     const SIZE: usize = 8;
//     const ALIGN: usize = 8;
//     // fn const_size_of() -> usize { 8 }
//     // fn const_align_of() -> usize { 8 }
// }

// // #[verifier::external]
// const SIZE_CHECK_U64: usize = (core::mem::size_of::<u64>() == u64::SIZE) as usize - 1;

// impl PmSized for crate::pmem::serialization_t::Test {
//     fn size_of() -> usize { Self::SIZE }
//     fn align_of() -> usize { Self::ALIGN }
// }

// impl ConstPmSized for crate::pmem::serialization_t::Test {
//     const SIZE: usize = u64::SIZE + u64::SIZE;
//     const ALIGN: usize = {
//         let mut largest_alignment = u64::ALIGN;
//         if u64::ALIGN > largest_alignment {
//             largest_alignment = u64::ALIGN;
//         }
//         largest_alignment
//     };
// }