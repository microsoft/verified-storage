//! This file contains the implementation of derive macros
//! for PmSafe and PmSized. These implementations are TRUSTED
//! and must be manually audited.

use proc_macro::TokenStream;
use syn::{self, spanned::Spanned};
use quote::{quote, quote_spanned};

pub fn generate_pmcopy(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let attrs = &ast.attrs;
    // Check that the structure is repr(C)
    if let Err(e) = check_repr_c(name, attrs) {
        return e;
    }

    let data = &ast.data;
    let (mut types, names) = match get_types(name, data) {
        Ok(types) => types,
        Err(e) => return e,
    };
    // Note: the vector of types may have duplicates -- this is not necessary
    // for all of the generated code, but some does depend on it, so we 
    // can't deduplicate here

    let pmsafe = check_pmsafe(ast, &types);
    match pmsafe {
        Ok(pmsafe) => {
            let pmsized = generate_pmsized(ast, &types);
            match pmsized {
                Ok(pmsized) => {
                    let cloneproof = generate_clone_proof(ast, &types, &names);
                    match cloneproof {
                        Ok(cloneproof) => {
                            let gen = quote!{
                                #cloneproof

                                #pmsafe

                                #pmsized

                                impl PmCopy for #name {}
                            };
                            gen.into()
                        }
                        Err(e) => e
                    }
                    
                }
                Err(e) => e,
            }
        }
        Err(e) => e,
    }
}

// This function is used by the PmSafe derive macro to check whether 
// a deriving type is, in fact, PmSafe. 
// All fields of the deriving type must be PmSafe. PmSafe primitive types are
// defined in storage_node/src/pmem/traits_t.rs. 
// 
// The repr(C) requirement is checked by checking the attributes of the deriving type.
// The PmSafe fields requirement is performed by adding trivial trait bounds to
// the unsafe implementation of PmSafe generated for the deriving type.
// For example, the generated implementation of PmSafe for the following type:
// ```
// struct Foo {
//      val1: u8,
//      val2: u16,
//      val3: u32
// }
// ```
// would look like:
// ```
// unsafe impl PmSafe for Foo
//      where u8: PmSafe, u16: PmSafe, u32: PmSafe {}
// ```
// These trait bounds are easily checkable by the compiler. Compilation will
// fail if we attempt to derive PmSafe on a struct with a field of type, e.g., 
// *const u8, as the bound `const *u8: PmSafe` is not met.
pub fn check_pmsafe<'a>(ast: &syn::DeriveInput, types: &Vec<&'a syn::Type>) -> Result<proc_macro2::TokenStream, TokenStream> {
    let name = &ast.ident;
    let gen = quote! {
        unsafe impl PmSafe for #name 
            where 
            #( #types: PmSafe, )*
        {}
    };
    Ok(gen)
}

// This function checks whether the struct has the repr(C) attribute so that we can
// trigger a compiler error if it doesn't. The repr(C) attribute ensures that the 
// structure has a consistent layout in memory, which is useful when reading and writing
// values to PM.
pub fn check_repr_c(name: &syn::Ident, attrs: &Vec<syn::Attribute>) ->  Result<(), TokenStream>  
{
    // look for an attribute with "repr(C)"
    for attr in attrs {
        let meta = &attr.meta;
        match meta {
            syn::Meta::List(list) => {
                if list.path.is_ident("repr") {
                    let tokens = proc_macro::TokenStream::from(list.tokens.clone());
                    for token in tokens.into_iter() {
                        match token {
                            proc_macro::TokenTree::Ident(ident) => {
                                if ident.to_string() == "C" {
                                    return Ok(());
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Err(quote_spanned! {
        name.span() =>
        compile_error!("PmSafe can only be derived for types with repr(C)");
    }.into())
}

// This function obtains a list of the types of the fields of a structure. We do not
// attempt to process the field names to keep things simple.
pub fn get_types<'a>(name: &'a syn::Ident, data: &'a syn::Data) -> Result<(Vec<&'a syn::Type>, Vec<syn::Ident>), TokenStream> 
{
    let mut type_vec = Vec::new();
    let mut name_vec = Vec::new();
    match data {
        syn::Data::Struct(data) => {
            let fields = &data.fields; 
            match fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let ty = &field.ty;
                        type_vec.push(ty);
                        // The borrow checker is annoying about the fact that field.ident has type Option<Ident>,
                        // so we have to clone the ident to put it in the vector. We know that the ident is not 
                        // None because we've already established that the fields are named.
                        let name = field.ident.clone().unwrap();
                        name_vec.push(name);
                    }
                    Ok((type_vec, name_vec))
                }
                _ => Err(
                    quote_spanned! {
                        name.span() =>
                        compile_error!("PmSafe can only be derived for structs with named fields");
                    }.into()
                )
            }
        }
        _ => {
            Err(quote_spanned! {
                name.span() =>
                compile_error!("PmSafe can only be derived for structs");
            }.into())
        }
    }
}

// This function generates an implementation of the PmSized trait for the PmSized
// derive macro. It also generates implementations for SpecPmSized, ConstPmSized,
// UnsafeSpecPmSized, and two compile-time assertions to check that we calculate
// the size of each type correctly.
pub fn generate_pmsized<'a>(ast: &syn::DeriveInput, types: &Vec<&'a syn::Type>) -> Result<proc_macro2::TokenStream, TokenStream> {
    let name = &ast.ident;

    // The size of a repr(C) struct is determined by the following algorithm, from the Rust reference:
    // https://doc.rust-lang.org/reference/type-layout.html#reprc-structs
    // "Start with a current offset of 0 bytes.
    // 
    // For each field in declaration order in the struct, first determine the size and alignment of the field.
    // If the current offset is not a multiple of the field's alignment, then add padding bytes to the current
    // offset until it is a multiple of the field's alignment. The offset for the field is what the current offset is
    // now. Then increase the current offset by the size of the field."
    // 
    // The required padding is calculated by the const fn `padding_needed`, which is implemented in the pmem module
    // and verified. We use the associated constants from ConstPmSized to obtain the alignment and size of the struct.
    //
    // Ideally the result of this code would be verified to match the result of the spec size code generated below,
    // but it is not currently possible to have const trait fn implementations in Rust, Verus' support for const 
    // trait impls is not mature enough and runs into panics in this project, so the const exec fns that calculate 
    // struct size can't be visible to the verifier. We could generate a non-associated constant fn for every 
    // struct that derives the trait, but generating such functions is tricky and ugly. 
    let mut exec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: usize = offset + <#ty>::SIZE + padding_needed(offset, <#ty>::ALIGN); 
        };
        exec_tokens_vec.push(new_tokens);
    }

    // We generate the size of a repr(C) struct in spec code using the same approach as in exec code, except we use 
    // spec functions to obtain the size, alignment, and padding needed. 
    let mut spec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: ::builtin::nat = offset + <#ty>::spec_size_of() + spec_padding_needed(offset, <#ty>::spec_align_of()); 
        };
        spec_tokens_vec.push(new_tokens);
    }

    // The alignment of a repr(C) struct is the alignment of the most-aligned field in it (i.e. the field with the largest
    // alignment). We currently unroll all of the fields and check which has the largest alignment without using a loop;
    // to make the generated code more concise, we could put the alignments in an array and use a while loop over it 
    // (for loops are not supported in const contexts).
    let mut exec_align_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            if largest_alignment <= <#ty>::ALIGN {
                largest_alignment = <#ty>::ALIGN;
            }
        };
        exec_align_vec.push(new_tokens);
    }

    // Since the executable implementation of alignment calculation requires a mutable value and/or a loop, it's not 
    // straightforward to generate an identical spec function for it. Instead, we just create a sequence of all of the 
    // alignments and find the maximum. If we ever want to prove that the alignment calculation is correct, the exec
    // side code generation will have to include proof code.
    let spec_alignment = quote! {
        let alignment_seq = seq![#(<#types>::spec_align_of(),)*];
        nat_seq_max(alignment_seq)
    };

    // This is the name of the constant that will perform the compile-time assertion that the calculated size of the struct
    // is equal to the real size. This is not an associated constant in an external trait implementation because the compiler 
    // will optimize the check out if it lives in an associated constant that is never used in any methods. In constrast,
    // it will always be evaluated if it is a standalone constant.
    let size_check = syn::Ident::new(&format!("SIZE_CHECK_{}", name.to_string().to_uppercase()), name.span());
    let align_check = syn::Ident::new(&format!("ALIGN_CHECK_{}", name.to_string().to_uppercase()), name.span());

    let gen = quote! {
        ::builtin_macros::verus!(

            impl SpecPmSized for #name {
                open spec fn spec_size_of() -> ::builtin::nat 
                {
                    let offset: ::builtin::nat = 0;
                    #( #spec_tokens_vec )*
                    offset
                }      

                open spec fn spec_align_of() -> ::builtin::nat 
                {
                    #spec_alignment
                }
            }  
        );

        unsafe impl PmSized for #name {
            fn size_of() -> usize { Self::SIZE }
            fn align_of() -> usize { Self::ALIGN }
        }

        unsafe impl ConstPmSized for #name {
            const SIZE: usize = {
                let offset: usize = 0;
                #( #exec_tokens_vec )*
                offset
            };
            const ALIGN: usize = {
                let mut largest_alignment: usize = 0;
                #( #exec_align_vec )*
                largest_alignment
            };
            
    }

    const #size_check: usize = (core::mem::size_of::<#name>() == <#name>::SIZE) as usize - 1;
    const #align_check: usize = (core::mem::align_of::<#name>() == <#name>::ALIGN) as usize - 1;

    unsafe impl UnsafeSpecPmSized for #name {}


    };
    Ok(gen)
}

pub fn generate_clone_proof<'a>(ast: &syn::DeriveInput, types: &Vec<&'a syn::Type>, names: &Vec<syn::Ident>) -> Result<proc_macro2::TokenStream, TokenStream>
{
    let name = &ast.ident;
    let lemma_name = syn::Ident::new(&format!("lemma_clone_{}", name.to_string().to_lowercase()), name.span());
    
    // TODO @hayley FRIDAY figure out why this isn't building...
    // it's a problem with ensures but not quite sure what
    let gen = quote!{
        ::builtin_macros::verus!{

            // impl CloneProof for #name {
            //     proof fn lemma_clone() 
            //         // where 
            //         //     #( #types: Clone, )*
            //             // #name: Clone,
            //         // requires    
            //         //     #( forall |a: #types, b: #types| ::builtin::imply(call_ensures(core::clone::Clone::clone, (&a,), b), a == b), )*
            //         // ensures 
            //         //     forall |a: #name, b: #name| ::builtin::imply(call_ensures(core::clone::Clone::clone, (&a,), b), a == b),
            //     {
            //         // #( lemma_clone::<#types>(); )*
            //         #( #types::lemma_clone(); )*

            //         assert(forall |a: #name, b: #name| ::builtin::imply(
            //             call_ensures(Clone::clone, (&a,), b), ::builtin::spec_eq(a, b)
            //         ));

            //         // assume(false); 
            //     }
            // }
        }
    };

    Ok(gen)
}

// For most types, alignment is the same as size on x86, EXCEPT for 
// u128/i128, which have an alignment of 8 bytes.
const BOOL_SIZE: usize = 1;
const CHAR_SIZE: usize = 4;
const I8_SIZE: usize = 1;
const I16_SIZE: usize = 2;
const I32_SIZE: usize = 4;
const I64_SIZE: usize = 8;
const I128_SIZE: usize = 16;
const I128_ALIGNMENT: usize = 16;
const ISIZE_SIZE: usize = 8;
const U8_SIZE: usize = 1;
const U16_SIZE: usize = 2;
const U32_SIZE: usize = 4;
const U64_SIZE: usize = 8;
const U128_SIZE: usize = 16;
const U128_ALIGNMENT: usize = 16;
const USIZE_SIZE: usize = 8;

// This function is called by the pmcopy_primitive! proc macro and generates an 
// implementation of PmSized, ConstPmSized, SpecPmSized, and UnsafeSpecPmSized
// primitive types. The verifier needs to be aware of their size and alignment at 
// verification time, so we provide this in the constants above and generate 
// implementations based on the values of these constants. The constants don't need
// to be audited, since the compile-time assertion will ensure they are correct,
// but we do need to manually ensure that the match statement in this function
// maps each type to the correct constant.
pub fn generate_pmcopy_primitive(ty: &syn::Type) -> TokenStream {
    let (size, align, ty_name) = match ty {
        syn::Type::Path(type_path) => {
            match type_path.path.get_ident() {
                Some(ident) => {
                    let ty_name = ident.to_string();
                    let (size, align) = match ty_name.as_str() {
                        "bool" => (BOOL_SIZE, BOOL_SIZE),
                        "char" => (CHAR_SIZE, CHAR_SIZE),
                        "i8" => (I8_SIZE, I8_SIZE),
                        "i16" => (I16_SIZE, I16_SIZE),
                        "i32" => (I32_SIZE, I32_SIZE),
                        "i64" => (I64_SIZE, I64_SIZE),
                        "i128" => (I128_SIZE, I128_ALIGNMENT),
                        "isize" => (ISIZE_SIZE, ISIZE_SIZE),
                        "u8" => (U8_SIZE, U8_SIZE),
                        "u16" => (U16_SIZE, U16_SIZE),
                        "u32" => (U32_SIZE, U32_SIZE),
                        "u64" => (U64_SIZE, U64_SIZE),
                        "u128" => (U128_SIZE, U128_ALIGNMENT),
                        "usize" => (USIZE_SIZE, USIZE_SIZE),
                        _ => {
                            return quote_spanned! {
                                ty.span() =>
                                compile_error!("pmcopy_primitive can only be used on primitive types");
                            }.into()
                        }
                        
                    };
                    (size, align, ty_name)
                }
                None => return quote_spanned! {
                    ty.span() =>
                    compile_error!("pmcopy_primitive can only be used on primitive types");
                }.into()
            }
        }
        _ => return quote_spanned! {
            ty.span() =>
            compile_error!("pmcopy_primitive can only be used on primitive types");
        }.into()
    };

    let size_check = syn::Ident::new(&format!("SIZE_CHECK_{}", ty_name.to_string().to_uppercase()), ty.span());
    let align_check = syn::Ident::new(&format!("ALIGN_CHECK_{}", ty_name.to_string().to_uppercase()), ty.span());

    // Primitive types have hardcoded size and alignment values
    let gen = quote!{
        ::builtin_macros::verus!(
            impl SpecPmSized for #ty {
                open spec fn spec_size_of() -> ::builtin::nat { #size as ::builtin::nat }
                open spec fn spec_align_of() -> ::builtin::nat { #align as ::builtin::nat }
            }

            impl CloneProof for #ty {
                proof fn lemma_clone() {}
            }
        );

        unsafe impl PmSized for #ty {
            fn size_of() -> usize { Self::SIZE }
            fn align_of() -> usize { Self::ALIGN }
        }

        unsafe impl ConstPmSized for #ty {
            const SIZE: usize = #size;
            const ALIGN: usize = #align;
        }

        const #size_check: usize = (core::mem::size_of::<#ty>() == <#ty>::SIZE) as usize - 1;
        const #align_check: usize = (core::mem::align_of::<#ty>() == <#ty>::ALIGN) as usize - 1;

        unsafe impl UnsafeSpecPmSized for #ty {}
    };
    gen.into()
}
