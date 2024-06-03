use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::bytes;
use vstd::bytes::*;
use vstd::prelude::*;
use vstd::ptr::*;
use vstd::layout::*;
use crate::pmem::markers_t::PmSafe;

use deps_hack::crc64fast::Digest;
use core::slice;
use std::convert::TryInto;
use std::ptr;
use std::mem::MaybeUninit;

verus! {
    // TODO: better name? "PmCopy" is not really accurate anymore. PmCopy?
    // Objects can only be written to PM if they derive PmSafe
    pub trait PmCopy : PmSized + Sized + PmSafe + Copy {}
    pub trait PmCopyHelper : PmCopy {
        spec fn spec_to_bytes(self) -> Seq<u8>;

        spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        // spec fn spec_size_of() -> nat;

        spec fn spec_crc(self) -> u64;

        exec fn size_of() -> (out: u64)
            ensures 
                out == Self::spec_size_of() as u64;

        exec fn as_byte_slice(&self) -> (out: &[u8])
            ensures 
                out@ == self.spec_to_bytes();

        spec fn size_inv(bytes: Seq<u8>) -> bool;

        proof fn axiom_bytes_len()
            ensures 
                forall |s: Self| #[trigger] s.spec_to_bytes().len() == Self::spec_size_of();

        // this seems like it might not be safe...
        proof fn axiom_to_from_bytes(self, bytes: Seq<u8>)
            ensures 
                self.spec_to_bytes() == bytes <==> self == Self::spec_from_bytes(bytes);
    }

    impl<T> PmCopyHelper for T where T: PmCopy {
        closed spec fn spec_to_bytes(self) -> Seq<u8>;

        closed spec fn spec_from_bytes(bytes: Seq<u8>) -> Self;

        // closed spec fn spec_size_of() -> nat;

        open spec fn spec_crc(self) -> u64 {
            spec_crc_u64(self.spec_to_bytes())
        }

        #[verifier::external_body]
        fn size_of() -> u64
        {
            core::mem::size_of::<Self>() as u64
        }

        #[verifier::external_body]
        exec fn as_byte_slice(&self) -> (out: &[u8])
        {
            let ptr = self as *const Self;
            unsafe { core::slice::from_raw_parts(ptr as *const u8, Self::size_of() as usize) }
        }

        open spec fn size_inv(bytes: Seq<u8>) -> bool
        {
            bytes.len() == Self::spec_size_of()
        }

        #[verifier::external_body]
        proof fn axiom_bytes_len() {}

        
        #[verifier::external_body]
        proof fn axiom_to_from_bytes(self, bytes: Seq<u8>) {}


    }

    // // This should be true for every PmCopy type, but making it default does not automatically
    // // make it true for all implementors and we can't put it in pre/postconditions of PmCopy
    // // methods due to cycle checking.
    // pub open spec fn spec_pmcopy_inv<S: PmCopy>() -> bool 
    // {
    //     &&& forall |s: S| {
    //             &&& #[trigger] s.spec_to_bytes().len() == S::spec_size_of()
    //             &&& #[trigger] s.spec_crc() == #[trigger] spec_crc_u64(s.spec_to_bytes())
    //             &&& s == #[trigger] S::spec_from_bytes(s.spec_to_bytes())
    //         }
    //     &&& forall |bytes: Seq<u8>, s: S| bytes == s.spec_to_bytes() ==> s == S::spec_from_bytes(bytes)        
    // }

    // u64 must implement PmCopy for CRC management
    impl PmCopy for u64 {}


    // is this name confusing?
    #[verifier::external_body]
    #[verifier::reject_recursive_types(S)]
    pub struct MaybeCorrupted<S>
        where 
            S: PmCopy
    {
        val: MaybeUninit<S>,
    }

    impl<S> MaybeCorrupted<S>
        where 
            S: PmCopy 
    {
        // The constructor doesn't have a postcondition because we do not know anything about 
        // the state of the bytes yet
        #[verifier::external_body]
        pub exec fn new() -> (out: Self)
        {
            MaybeCorrupted { 
                val: MaybeUninit::uninit()
            }
        }

        pub closed spec fn view(self) -> Seq<u8>;

        #[verifier::external_body]
        pub exec fn copy_from_slice(
            &mut self, 
            bytes: &[u8], 
            Ghost(true_val): Ghost<S>,
            Ghost(addrs): Ghost<Seq<int>>,
            Ghost(impervious_to_corruption): Ghost<bool>
        )
            requires 
                if impervious_to_corruption {
                    bytes@ == true_val.spec_to_bytes()
                } else {
                    maybe_corrupted(bytes@, true_val.spec_to_bytes(), addrs)
                },
                bytes@.len() == S::spec_size_of(),
            ensures 
                self@ == bytes@
        {
            self.copy_from_slice_helper(bytes);
        }

        // TODO: remove this helper function and move its body back into `copy_from_slice` once 
        // https://github.com/verus-lang/verus/issues/1151 is fixed
        #[verifier::external]
        #[inline(always)]
        fn copy_from_slice_helper(
            &mut self, 
            bytes: &[u8], 
        ) 
        {
            // convert the MaybeUninit<S> to a mutable slice of `MaybeUninit<u8>`
            let mut self_bytes = self.val.as_bytes_mut();
            // copy bytes from the given slice to the mutable slice of `MaybeUninit<u8>`.
            // This returns a slice of initialized bytes, but it does NOT change the fact that 
            // the original S is still MaybeUninit
            // TODO: in newer versions of Rust, write_slice is renamed to copy_from_slice
            MaybeUninit::write_slice(self_bytes, bytes);
        }


        #[verifier::external_body]
        pub exec fn as_slice(&self) -> (out: &[u8])
            ensures 
                out@ == self@
        {
            let bytes = self.val.as_bytes();
            // SAFETY: even if we haven't initialized the bytes, there are no invalid values of u8, so we can 
            // safely assume that these bytes are initialized (even if the S may not be)
            unsafe { MaybeUninit::slice_assume_init_ref(bytes) }
        }

        #[verifier::external_body]
        pub exec fn extract_init_val(self, Ghost(true_val): Ghost<S>) -> (out: S)
            requires 
                self@ == true_val.spec_to_bytes()
            ensures 
                out == true_val
        {
            // SAFETY: The precondition establishes that self@ -- the ghost view of the maybe-corrupted bytes
            // written to self.val -- are equivalent to the serialization of the true value; i.e., we must have 
            // proven that the bytes are not corrupted, and therefore self.val is initialized.
            unsafe { self.val.assume_init() }
        }
    }

    // Right now unaligned reads return vecs and Verus can't easily switch between Vec/slice,
    // so we use a separate spec fn to specify that a vector lives in volatile memory (even
    // though that should always be the case anyway)
    // TODO: is this actually necessary? NO- remove
    pub closed spec fn vec_is_volatile(bytes: Vec<u8>) -> bool;


    pub trait PmSized: PmSafe {
        spec fn spec_size_of() -> nat;
    }

    global size_of usize == 8;
    global size_of isize == 8;

    // TODO: this macro doesn't work if there are any non-pub fields.
    macro_rules! pm_sized{
        ($v:vis struct $name:ident { $(pub $f_name:ident: $f_type:ty),* $(,)? }) => {
            ::builtin_macros::verus! {
                #[repr(C)]
                #[derive(PmSafe, Copy, Clone)]
                $v struct $name { 
                    $(
                    pub $f_name: $f_type,
                    )*
                }
                impl PmSized for $name {
                    open spec fn spec_size_of() -> nat {
                        $(
                            (<$f_type>::spec_size_of())+
                        )*
                        0
                    }
                }
            }
        };
    }

    pub(crate) use pm_sized;

    // Manual trusted implementations of PmSized for safe primitive types.
    // The sizes of all other types are derived from these. They should be audited
    // to ensure they match the actual sizes of the types. We specify earlier 
    // that usize and isize are 8 bytes
    impl PmSized for u8 {
        open spec fn spec_size_of() -> nat {
            1
        }
    }
    impl PmSized for u16 {
        open spec fn spec_size_of() -> nat {
            2
        }
    }
    impl PmSized for u32 {
        open spec fn spec_size_of() -> nat {
            4
        }
    }
    impl PmSized for u64 {
        open spec fn spec_size_of() -> nat {
            8
        }
    }
    impl PmSized for u128 {
        open spec fn spec_size_of() -> nat {
            16
        }
    }
    impl PmSized for usize {
        open spec fn spec_size_of() -> nat {
            8
        }
    }
    impl PmSized for i8 {
        open spec fn spec_size_of() -> nat {
            1
        }
    }
    impl PmSized for i16 {
        open spec fn spec_size_of() -> nat {
            2
        }
    }
    impl PmSized for i32 {
        open spec fn spec_size_of() -> nat {
            4
        }
    }
    impl PmSized for i64 {
        open spec fn spec_size_of() -> nat {
            8
        }
    }
    impl PmSized for i128 {
        open spec fn spec_size_of() -> nat {
            16
        }
    }
    impl PmSized for isize {
        open spec fn spec_size_of() -> nat {
            8
        }
    }
    impl<T: PmSized, const N: usize> PmSized for [T; N] {
        open spec fn spec_size_of() -> nat {
            (N * T::spec_size_of()) as nat
        }
    }
    impl PmSized for bool {
        open spec fn spec_size_of() -> nat {
            1
        }
    }
    impl PmSized for char {
        open spec fn spec_size_of() -> nat {
            4
        }
    }
    // impl PmSized for f32 {
    //     open spec fn spec_size_of() -> nat {
    //         4
    //     }
    // }
    // impl PmSized for f64 {
    //     open spec fn spec_size_of() -> nat {
    //         8
    //     }
    // }

}