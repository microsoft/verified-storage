use std::cell::UnsafeCell;
use std::fmt;

use builtin_macros::*;
use builtin::*;
use vstd::prelude::*;

/// It marks the implementing type to be free of pointers to the volatile heap,
/// and persistence safe.
///
/// Also, every type that allows interior mutability is not safe in persistence
/// terms, because there might be no log of the value. Atomic types are
/// persistence safe, even though they provide interior mutability.
/// 
/// # Limitation
/// 
/// Function pointers are not completely prevented. Due to Rust's limitation on
/// declaring generic pointers to functions without exact number of arguments,
/// we manually limit all pointers to functions with up to 32 arguments. Function
/// pointers with a number of arguments beyond 32 are inevitably allowed.
/// 
#[rustc_on_unimplemented(
    message = "`{Self}` is not safe to be stored in persistent memory",
    label = "`{Self}` is not safe to be stored in persistent memory"
)]
pub unsafe auto trait PSafe {}

impl<T: ?Sized> !PSafe for *const T {}
impl<T: ?Sized> !PSafe for *mut T {}
impl<T> !PSafe for &T {}
impl<T> !PSafe for &mut T {}
impl !PSafe for std::fs::File {}

impl<R> !PSafe for fn()->R {}

macro_rules! not_safe {
    ($($a:ident),*) => {
        impl<$($a),* , R> !PSafe for fn($($a),*)->R {}
    };
}

not_safe!(A1);
not_safe!(A1,A2);
not_safe!(A1,A2,A3);
not_safe!(A1,A2,A3,A4);
not_safe!(A1,A2,A3,A4,A5);
not_safe!(A1,A2,A3,A4,A5,A6);
not_safe!(A1,A2,A3,A4,A5,A6,A7);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28,A29);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28,A29,A30);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28,A29,A30,A31);
not_safe!(A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28,A29,A30,A31,A32);

/// `UnsafeCell` is marked as PSafe because it exposes interior mutability
/// without taking a log, which is unsafe from persistence perspective.
impl<T: ?Sized> !PSafe for UnsafeCell<T> {}

verus! {
    #[verifier::external_trait_specification]
    pub trait ExPSafe {
        type ExternalTraitSpecificationFor: PSafe;
    }
}