//! This file contains the implementation several macros
//! to implement PmCopy-related traits.
//! These implementations are TRUSTED and must be manually audited.

use proc_macro::TokenStream;
use syn::{self, spanned::Spanned};
use quote::{quote, quote_spanned};

// each enum variant may have multiple (or no) fields, but within
// a single variant they will all be named or unnamed.
enum EnumVariantFields {
    Unit,
    Named(Vec<syn::Type>, Vec<syn::Ident>),
    Unnamed(Vec<syn::Type>)
}

enum LayoutType {
    NamedStruct(Vec<syn::Type>, Vec<syn::Ident>),
    UnnamedStruct(Vec<syn::Type>),
    FieldlessEnum(Vec<syn::Ident>),
    EnumWithFields(Vec<syn::Ident>, Vec<EnumVariantFields>),
    Union(Vec<syn::Type>, Vec<syn::Ident>),
}

// This is the main function called by the PmCopy derive macro.
// It calls functions to check that structures are PmSafe,
// implementations for PmSized-related traits, and methods
// to help reason about cloning PmCopy objects.
// Methods must be repr(C) to derive PmCopy.
pub fn generate_pmcopy(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let attrs = &ast.attrs;
    // Check that the structure is repr(C)
    if let Err(e) = check_repr_c(name, attrs) {
        return e;
    }

    let data = &ast.data;
    let layout_type = match get_types(name, data) {
        Ok(types) => types,
        Err(e) => return e,
    };
    // Note: the vector of types may have duplicates -- this is not necessary
    // for all of the generated code, but some does depend on it, so we 
    // can't deduplicate here

    match layout_type {
        LayoutType::NamedStruct(types, idents) => generate_impls_for_named_struct(&name, &types, &idents).into(),
        LayoutType::UnnamedStruct(types) => generate_impls_for_unnamed_struct(&name, &types).into(),
        LayoutType::FieldlessEnum(variants) => generate_impls_for_fieldless_enum(&name, &variants).into(),
        LayoutType::EnumWithFields(variants, fields) => generate_impls_for_enum_with_fields(&name, &variants, &fields),
        LayoutType::Union(types, idents) => generate_impls_for_union(&name, &types, &idents).into(),
    }
}

fn generate_impls_for_named_struct(
    name: &syn::Ident,
    types: &Vec<syn::Type>, 
    names: &Vec<syn::Ident>
) -> proc_macro2::TokenStream {
    let pmcopy = check_pmcopy(&name, &types);
    match pmcopy {
        Ok(pmcopy) => {
            let pmsized = generate_pmsized_for_structs(name, &types);
            let cloneproof = generate_clone_proof_for_named_structs(name, &names);
            let gen = quote!{
                #pmcopy

                #pmsized

                #cloneproof

                impl PmCopy for #name {}
            };
            gen
        }
        Err(e) => e.into(),
    }
}

fn generate_impls_for_unnamed_struct(
    name: &syn::Ident,
    types: &Vec<syn::Type>,
) -> proc_macro2::TokenStream {
    let pmcopy = check_pmcopy(&name, &types);
    match pmcopy {
        Ok(pmcopy) => {
            let pmsized = generate_pmsized_for_structs(name, &types);
            let cloneproof = generate_clone_proof_for_unnamed_structs(name, &types);
            let gen = quote!{
                #pmcopy

                #pmsized

                #cloneproof

                impl PmCopy for #name {}
            };
            gen
        }
        Err(e) => e.into(),
    }
}

const C_ABI_ENUM_SIZE: usize = 4;
const C_ABI_ENUM_ALIGN: usize = 4;
const ZST_SIZE: usize = 0;
const ZST_ALIGN: usize = 1;

fn generate_pmsized_for_fieldless_enum(
    name: &syn::Ident,
) -> proc_macro2::TokenStream {
    let gen = quote! {
        ::builtin_macros::verus!(
            impl SpecPmSized for #name {
                open spec fn spec_size_of() -> ::builtin::nat
                { 
                    #C_ABI_ENUM_SIZE as ::builtin::nat
                }

                open spec fn spec_align_of() -> ::builtin::nat
                {
                    #C_ABI_ENUM_ALIGN as ::builtin::nat
                }
            }
        );

        unsafe impl PmSized for #name {
            fn size_of() -> usize { Self::SIZE }
            fn align_of() -> usize { Self::ALIGN }
        }

        unsafe impl ConstPmSized for #name {
            const SIZE: usize = #C_ABI_ENUM_SIZE;
            const ALIGN: usize = #C_ABI_ENUM_ALIGN;
        }

        unsafe impl UnsafeSpecPmSized for #name {}
    };

    gen
}

// repr(C) enums with fields have the layout of a #[repr(C)] struct
// with two fields, the tag and the payload. 
// The tag is a repr(C) version of the enum with the fields removed.
// The payload is a repr(C) union of repr(C) structs, each of which 
// has the fields of one of the variants.
fn generate_pmsized_for_enums_with_fields(
    name: &syn::Ident,
    variants: &Vec<syn::Ident>,
    fields: &Vec<EnumVariantFields>,
) -> proc_macro2::TokenStream {

    // Generate the payload structs first
    let mut payload_defs_and_impls = Vec::new();
    let mut payload_struct_names = Vec::new();
    let mut payload_struct_types = Vec::new();

    for (variant, variant_fields) in variants.iter().zip(fields.iter()) {
        // TODO: what should spans be in here?
        let struct_name = syn::Ident::new(&format!("{}{}Fields", name.to_string(), variant), variant.span());
        let static_assertions = generate_static_assertions(&struct_name);
        
        payload_struct_names.push(struct_name.clone());
        payload_struct_types.push(syn::Type::Verbatim(quote! {#struct_name} ));

        match variant_fields {
            EnumVariantFields::Unit => {
                let gen = quote! {
                    ::builtin_macros::verus! {
                        #[repr(C)]
                        #[derive(Copy)]
                        struct #struct_name {}

                        impl SpecPmSized for #struct_name {
                            open spec fn spec_size_of() -> ::builtin::nat { #ZST_SIZE as ::builtin::nat }
                            open spec fn spec_align_of() -> ::builtin::nat { #ZST_ALIGN as ::builtin::nat }
                        }
                    }

                    unsafe impl PmSafe for #struct_name {}

                    unsafe impl PmSized for #struct_name {
                        fn size_of() -> usize { Self::SIZE }
                        fn align_of() -> usize { Self::ALIGN }
                    }

                    unsafe impl ConstPmSized for #struct_name {
                        const SIZE: usize = #ZST_SIZE;
                        const ALIGN: usize = #ZST_ALIGN;
                    }

                    unsafe impl UnsafeSpecPmSized for #struct_name {}

                    #static_assertions

                    impl Clone for #struct_name {
                        fn clone(&self) -> Self {
                            *self
                        }
                    }

                    impl PartialEq for #struct_name {
                        fn eq(&self, other: &Self) -> bool 
                        {
                            // two instances of the same ZST are always equal
                            true
                        }
                    }
                };
                payload_defs_and_impls.push(gen);
            }
            EnumVariantFields::Unnamed(types) => {
                let impls = generate_impls_for_unnamed_struct(&struct_name, types);
                let gen = quote! {
                    ::builtin_macros::verus! {
                        #[repr(C)]
                        #[derive(Copy)]
                        struct #struct_name( #( #types, )* );
                    }

                    #impls
                };
                payload_defs_and_impls.push(gen);
            }
            EnumVariantFields::Named(types, names) => {
                let impls = generate_impls_for_named_struct(&struct_name, types, names);
                let mut lowercase_names = Vec::new();
                for n in names.iter() {
                    lowercase_names.push(syn::Ident::new(&n.to_string().to_lowercase(), n.span()));
                }
                let gen = quote! {
                    ::builtin_macros::verus! {
                        #[repr(C)]
                        #[derive(Copy)]
                        struct #struct_name {
                            #( #lowercase_names: #types, )*
                        }
                    }

                    #impls
                };
                payload_defs_and_impls.push(gen);
            }
        }
    }

    let mut lowercase_variant_names = Vec::new();
    for v in variants {
        lowercase_variant_names.push(syn::Ident::new(&v.to_string().to_lowercase(), v.span()));
    }

    // generate the union of payload structs and impls for it
    let union_name = syn::Ident::new(&format!("{}FieldUnion", name.to_string()), name.span());
    let union_impls = generate_impls_for_union(&union_name, &payload_struct_types, &lowercase_variant_names);
    let payload_union = quote! {
        ::builtin_macros::verus! {
            #[repr(C)]
            #[derive(Copy)]
            union #union_name {
                #( #lowercase_variant_names: #payload_struct_names, )*
            }
        }

        #union_impls
    };

    // generate the discriminant enum definition and impls
    let discriminant_enum_name = syn::Ident::new(&format!("{}EnumDiscriminant", name.to_string()), name.span());
    let discriminant_enum_impls = generate_impls_for_fieldless_enum(&discriminant_enum_name, &variants);
    let discriminant_enum = quote! {
        ::builtin_macros::verus!{ 
            #[repr(C)]
            #[derive(Copy)]
            enum #discriminant_enum_name {
                #( #variants, )*
            }
        }
        
        #discriminant_enum_impls
    };

    let final_struct_field_names = vec![syn::Ident::new("tag", name.span()), syn::Ident::new("payload", name.span())];
    let final_struct_field_types = vec![syn::Type::Verbatim(quote! {#discriminant_enum_name} ), syn::Type::Verbatim(quote! {#union_name} )];
    
    let final_struct_name = syn::Ident::new(&format!("{}LayoutStruct", name.to_string()), name.span());
    let final_struct_impls = generate_impls_for_named_struct(
        &final_struct_name, &final_struct_field_types, &final_struct_field_names);

    let final_struct = quote! {
        ::builtin_macros::verus! {
            #[repr(C)]
            #[derive(Copy)]
            struct #final_struct_name {
                #( #final_struct_field_names: #final_struct_field_types,)*
            }
        }
        
        #final_struct_impls
    };

    let static_assertions = generate_static_assertions(&name);
    let eq_and_clone_proof = generate_clone_and_eq_proofs_for_enum_with_fields(&name, variants, fields);

    // Now we can implement everything for the initial enum itself
    // using the structs and impls we have just generated.
    let enum_impls = quote! {
        ::builtin_macros::verus!{
            impl SpecPmSized for #name {
                open spec fn spec_size_of() -> ::builtin::nat 
                {
                    #final_struct_name::spec_size_of()
                }

                open spec fn spec_align_of() -> ::builtin::nat 
                {
                    #final_struct_name::spec_align_of()
                }
            }
        }

        unsafe impl PmSized for #name {
            fn size_of() -> usize { Self::SIZE }
            fn align_of() -> usize { Self::ALIGN }
        }

        unsafe impl ConstPmSized for #name {
            const SIZE: usize = #final_struct_name::SIZE;
            const ALIGN: usize = #final_struct_name::ALIGN;
        }

        unsafe impl UnsafeSpecPmSized for #name {}

        #static_assertions

        #eq_and_clone_proof      
    };


    let gen = quote! {
        #( #payload_defs_and_impls)*

        #payload_union

        #discriminant_enum

        #final_struct

        #enum_impls
    };
    gen

}

// Fieldless enums are always PmSafe. Their size and alignment matches 
// those used by the target platforms C ABI, which we expect to be 4 bytes.
// This function generates impls/specs for PmSized and related traits, Clone,
// and Eq for fieldless enums. The PartialEq implementation requires a list 
// of variant idents so that it can match on them, but otherwise we 
// can ignore them.
fn generate_impls_for_fieldless_enum(
    name: &syn::Ident,
    idents: &Vec<syn::Ident>,
) -> proc_macro2::TokenStream {
    // fieldless enums are always PmSafe

    let pmsized = generate_pmsized_for_fieldless_enum(name);
    let eq_and_clone_proof = generate_clone_and_eq_proofs_for_fieldless_enum(name, idents);
    let static_assertions = generate_static_assertions(&name);

    let gen = quote! {
        #pmsized

        unsafe impl PmSafe for #name {}

        impl PmCopy for #name {}

        #eq_and_clone_proof

        #static_assertions
    };

    gen
}


fn generate_impls_for_enum_with_fields(
    name: &syn::Ident,
    variants: &Vec<syn::Ident>,
    fields: &Vec<EnumVariantFields>,
) -> TokenStream {
    // enums with fields are only PmSafe if all fields types are PmSafe.
    // we have to do a little more work to get the types out in this case
    let mut types = Vec::new();
    for variant_field_list in fields {
        match variant_field_list {
            EnumVariantFields::Unit => {},
            EnumVariantFields::Named(variant_types, _) | EnumVariantFields::Unnamed(variant_types)=> {
                types.extend(variant_types.clone());
            }
        }
    }
    let pmcopy = check_pmcopy(&name, &types);
    match pmcopy {
        Ok(pmcopy) => {
            let pmsized = generate_pmsized_for_enums_with_fields(name, variants, fields);
            let gen = quote! {
                #pmcopy

                #pmsized

                impl PmCopy for #name {}
            };

            gen.into()
        }
        Err(e) => e,
    }
}

fn generate_impls_for_union(
    name: &syn::Ident,
    types: &Vec<syn::Type>, 
    names: &Vec<syn::Ident>
) -> proc_macro2::TokenStream {
    // Like structs, unions are only PmSafe if all of their fields
    // are PmSafe.
    let pmcopy = check_pmcopy(&name, &types);
    match pmcopy {
        Ok(pmcopy) => {
            let pmsized = generate_pmsized_for_unions(name, types);
            let cloneproof = generate_clone_and_eq_proofs_for_union(name, names);
            let gen = quote! {
                #pmcopy 

                #pmsized 

                #cloneproof 

                impl PmCopy for #name {}
            };
            gen
        }
        Err(e) => e.into(),
    }
}

// This function checks whether a given structure is PmSafe and, if it is, generates
// an implementation of PmSafe.
// All fields of the deriving type must be PmSafe. PmSafe primitive types are
// defined in capybarakv/src/pmem/traits_t.rs. 
// 
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
pub fn check_pmcopy(name: &syn::Ident, types: &Vec<syn::Type>) -> Result<proc_macro2::TokenStream, TokenStream> {
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
    let mut has_repr_c = false;
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
                                    has_repr_c = true;
                                } else {
                                    return Err(quote_spanned! {
                                        ident.span().into() =>
                                        compile_error!("PmCopy currently does not support representations other than repr(C).");
                                    }.into());
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
    if has_repr_c {
        Ok(())
    } else {
        Err(quote_spanned! {
            name.span() =>
            compile_error!("PmSafe can only be derived for types with repr(C)");
        }.into())
    }
}

// This function obtains a list of the types of the fields of a structure. We do not
// attempt to process the field names to keep things simple.
fn get_types(name: &syn::Ident, data: &syn::Data) -> Result<LayoutType, TokenStream> 
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
                        type_vec.push(ty.clone());
                        // The borrow checker is annoying about the fact that field.ident has type Option<Ident>,
                        // so we have to clone the ident to put it in the vector. We know that the ident is not 
                        // None because we've already established that the fields are named.
                        let name = field.ident.clone().unwrap();
                        name_vec.push(name);
                    }
                    Ok(LayoutType::NamedStruct(type_vec, name_vec))
                }
                syn::Fields::Unnamed(fields) => {
                    for field in fields.unnamed.iter() {
                        type_vec.push(field.ty.clone());
                    }
                    Ok(LayoutType::UnnamedStruct(type_vec))
                }
                _ => Err(quote_spanned! {
                    name.span() => compile_error!("PmCopy cannot be derive on structs with unit fields")
                }.into())
            }
        }
        syn::Data::Enum(data) => {
            let mut variant_vec = Vec::new();
            let mut field_vec = Vec::new();
            let mut has_fields = false;

            let variants = &data.variants;
            for variant in variants.iter() {
                // add each variant to the list of variants
                variant_vec.push(variant.ident.clone());
                // handle the variant's fields, if there are any
                match &variant.fields {
                    syn::Fields::Unit => field_vec.push(EnumVariantFields::Unit),
                    syn::Fields::Unnamed(fields) => {
                        has_fields = true;
                        let mut field_types = Vec::new();
                        for field in fields.unnamed.iter() {
                            field_types.push(field.ty.clone());
                        }
                        field_vec.push(EnumVariantFields::Unnamed(field_types));
                    }
                    syn::Fields::Named(fields) => {
                        has_fields = true;
                        let mut field_types = Vec::new();
                        let mut field_names = Vec::new();
                        for field in fields.named.iter() {
                            field_types.push(field.ty.clone());
                            field_names.push(field.ident.clone().unwrap());
                        }
                        field_vec.push(EnumVariantFields::Named(field_types, field_names));
                    }
                }
            }

            if has_fields {
                Ok(LayoutType::EnumWithFields(variant_vec, field_vec))
            } else {
                Ok(LayoutType::FieldlessEnum(variant_vec))
            }
        }
        syn::Data::Union(data) => {
            let mut name_vec = Vec::new();
            let mut type_vec = Vec::new();

            let fields = &data.fields;
            for field in fields.named.iter() {
                let ty = &field.ty;
                type_vec.push(ty.clone());
                // The borrow checker is annoying about the fact that field.ident has type Option<Ident>,
                // so we have to clone the ident to put it in the vector. We know that the ident is not 
                // None because we've already established that the fields are named.
                let name = field.ident.clone().unwrap();
                name_vec.push(name);
            }
            Ok(LayoutType::Union(type_vec, name_vec))
        }
    }
}

fn generate_size_check_ident(name: &syn::Ident) -> (syn::Ident, syn::Ident) {
    // This is the name of the constant that will perform the compile-time assertion that the calculated size of the struct
    // is equal to the real size. This is not an associated constant in an external trait implementation because the compiler 
    // will optimize the check out if it lives in an associated constant that is never used in any methods. In constrast,
    // it will always be evaluated if it is a standalone constant.
    let size_check = syn::Ident::new(&format!("SIZE_CHECK_{}", name.to_string().to_uppercase()), name.span());
    let align_check = syn::Ident::new(&format!("ALIGN_CHECK_{}", name.to_string().to_uppercase()), name.span());
    (size_check, align_check)
}

fn generate_static_assertions(name: &syn::Ident) -> proc_macro2::TokenStream {
    let (size_check, align_check) = generate_size_check_ident(name);
    let gen = quote! {
        const #size_check: usize = (core::mem::size_of::<#name>() == <#name>::SIZE) as usize - 1;
        const #align_check: usize = (core::mem::align_of::<#name>() == <#name>::ALIGN) as usize - 1;
    };
    gen
}

// First return value is the exec code to find the largest field, second is corresponding spec code
fn max_alignment_of_fields(types: &Vec<syn::Type>) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    // The alignment of a repr(C) struct or union is the alignment of the most-aligned field in it (i.e. the field with the largest
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
    let exec_alignment = quote! {
        let mut largest_alignment: usize = 0;
        #( #exec_align_vec )*
        largest_alignment
    };

    // Since the executable implementation of alignment calculation requires a mutable value and/or a loop, it's not 
    // straightforward to generate an identical spec function for it. Instead, we just create a sequence of all of the 
    // alignments and find the maximum. If we ever want to prove that the alignment calculation is correct, the exec
    // side code generation will have to include proof code.
    let spec_alignment = quote! {
        let alignment_seq = seq![#(<#types>::spec_align_of(),)*];
        nat_seq_max(alignment_seq)
    };

    (exec_alignment, spec_alignment)
}

fn max_size_of_fields(name: &syn::Ident, types: &Vec<syn::Type>) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let mut exec_size_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            if largest_size <= <#ty>::SIZE {
                largest_size = <#ty>::SIZE;
            }
        };
        exec_size_vec.push(new_tokens);
    }
    let final_token = quote! {
        let largest_size: usize = largest_size + padding_needed(largest_size, <#name>::ALIGN);
    };
    exec_size_vec.push(final_token);
    let exec_size = quote! {
        let mut largest_size: usize = 0;
        #( #exec_size_vec )*
        largest_size
    };

    let spec_size = quote! {
        let size_seq = seq![#(<#types>::spec_size_of(),)*];
        let largest_size = nat_seq_max(size_seq);
        let largest_size = largest_size + spec_padding_needed(largest_size, <#name>::spec_align_of());
        largest_size
    };

    (exec_size, spec_size)
}

// NOTE: this function does not add the final token required to correctly calculate the size 
fn exec_struct_size(types: &Vec<syn::Type>) -> Vec<proc_macro2::TokenStream> {
    let mut exec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: usize = offset + <#ty>::SIZE + padding_needed(offset, <#ty>::ALIGN); 
        };
        exec_tokens_vec.push(new_tokens);
    }
    exec_tokens_vec
}

fn spec_struct_size(types: &Vec<syn::Type>) -> Vec<proc_macro2::TokenStream> {
    let mut spec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: ::builtin::nat = offset + <#ty>::spec_size_of() + spec_padding_needed(offset, <#ty>::spec_align_of()); 
        };
        spec_tokens_vec.push(new_tokens);
    }
    spec_tokens_vec
}

// This function generates an implementation of PmSized. 
// It also generates implementations for SpecPmSized, ConstPmSized,
// UnsafeSpecPmSized, and two compile-time assertions to check that we calculate
// the size of each type correctly.
pub fn generate_pmsized_for_structs(name: &syn::Ident, types: &Vec<syn::Type>) -> proc_macro2::TokenStream {
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
    
    let mut exec_tokens_vec = exec_struct_size(types);
    let final_token = quote! {
        let offset: usize = offset + padding_needed(offset, <#name>::ALIGN);
    };
    exec_tokens_vec.push(final_token);

    // We generate the size of a repr(C) struct in spec code using the same approach as in exec code, except we use 
    // spec functions to obtain the size, alignment, and padding needed. 
    let mut spec_tokens_vec = spec_struct_size(types);
    let final_token = quote! {
        let offset: ::builtin::nat = offset + spec_padding_needed(offset, <#name>::spec_align_of());
    };
    spec_tokens_vec.push(final_token);

    let (exec_alignment, spec_alignment) = max_alignment_of_fields(types);

    let static_assertions = generate_static_assertions(&name);

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
                #exec_alignment
            };  
        }

        #static_assertions

        unsafe impl UnsafeSpecPmSized for #name {}
    };

    gen
}

fn generate_pmsized_for_unions(
    name: &syn::Ident, 
    types: &Vec<syn::Type>
) -> proc_macro2::TokenStream {
    // The size of a repr(C) union is the maximum size 
    // of all of its fields rounded to its alignment, and 
    // its alignment is the maximum alignment of all of its fields.
    // Note that the max size and max alignment may come from
    // different fields!

    // This function generates code to find the maximum size of 
    // all of the fields, then rounds up to the alignment of
    // the largest field. We haven't generated the alignment-calculating
    // code yet, but since we don't run that code here, it doesn't matter.
    let (exec_size, spec_size) = max_size_of_fields(name, types);

    // Union and struct alignment is calculated in the same way, so 
    // we use the same function for them.
    let (exec_alignment, spec_alignment) = max_alignment_of_fields(types);

    let static_assertions = generate_static_assertions(&name);

    let gen = quote! {
        ::builtin_macros::verus!(
            impl SpecPmSized for #name {
                open spec fn spec_size_of() -> ::builtin::nat
                {
                    #spec_size
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
                #exec_size
            };
            const ALIGN: usize = {
                #exec_alignment
            };
        }

        #static_assertions

        unsafe impl UnsafeSpecPmSized for #name {}
    };

    gen
}

// This function generates the following for a type deriving PmCopy:
// 1. An implementation of the `Clone` trait 
// 2. A specification of `Clone::clone` that matches the generated impl
// 3. An implementation of the `CloneProof` trait that makes it easier
//    to reason about cloning generic PmCopy objects.
pub fn generate_clone_proof_for_named_structs(name: &syn::Ident, names: &Vec<syn::Ident>) -> proc_macro2::TokenStream
{
    let first_n_names = &names[0..names.len()-1];
    let last_name = &names[names.len()-1];

    let eq_and_clone_spec = generate_eq_and_clone_specs(&name);

    let gen = quote!{
        // to ensure that the deriver does not provide a conflicting implementation 
        // of Clone, we implement it here.
        // Since the only way to generate these functions also implements PmSafe,
        // all fields must also implement PmSafe and thus also have a generated
        // Clone impl, so the clone calls on fields will also give the 
        // expected output.
        impl Clone for #name {
            fn clone(&self) -> Self 
            {
                Self {
                    #( #names: self.#names.clone(), )*
                }
            }
        }

        // Same with PartialEq -- providing an implementation here ensures 
        // that clients cannot provide an incorrect implementation for their 
        // own PmCopy types.
        impl PartialEq for #name {
            fn eq(&self, other: &Self) -> bool
            {
                #( self.#first_n_names == other.#first_n_names && )*
                self.#last_name == other.#last_name
            } 
        }

        #eq_and_clone_spec
        
    };

    gen
}

fn generate_clone_proof_for_unnamed_structs(
    name: &syn::Ident,
    types: &Vec<syn::Type>
) -> proc_macro2::TokenStream {
    let eq_and_clone_spec = generate_eq_and_clone_specs(&name);
    let field_nums: Vec<usize> = (0..types.len()-1).collect();
    let mut field_idxes = Vec::new();
    for i in field_nums {
        field_idxes.push(syn::Index::from(i));
    }
    let last_field_num = syn::Index::from(types.len()-1);

    let gen = quote! {
        impl Clone for #name {
            fn clone(&self) -> Self 
            {
                *self
            }
        }

        impl PartialEq for #name {
            fn eq(&self, other: &Self) -> bool 
            {
                #( self.#field_idxes == other.#field_idxes && )*
                self.#last_field_num == other.#last_field_num
            }
        }

        #eq_and_clone_spec
    };

    gen
}

fn generate_clone_and_eq_proofs_for_fieldless_enum(
    name: &syn::Ident,
    idents: &Vec<syn::Ident>,
) -> proc_macro2::TokenStream {
    let eq_and_clone_spec = generate_eq_and_clone_specs(&name);

    let gen = quote! {
        impl Clone for #name {
            fn clone(&self) -> Self 
            {
                *self
            }
        }

        impl PartialEq for #name {
            fn eq(&self, other: &Self) -> bool 
            {
                match (self, other) {
                    #( (#name::#idents, #name::#idents) => true, )*
                    (_, _) => false
                }
            }
        }

        #eq_and_clone_spec
    };

    gen
}

fn generate_clone_and_eq_proofs_for_enum_with_fields(
    name: &syn::Ident,
    variants: &Vec<syn::Ident>,
    fields: &Vec<EnumVariantFields>
) -> proc_macro2::TokenStream {
    let eq_and_clone_specs = generate_eq_and_clone_specs(&name);

    let mut eq_vec = Vec::new();

    for (variant, variant_fields) in variants.iter().zip(fields.iter()) {
        match variant_fields {
            EnumVariantFields::Unit => {
                // for unit variants, two enums are equal if they are 
                // the same variant
                let gen = quote! {
                    (#name::#variant, #name::#variant) => true
                };
                eq_vec.push(gen);
            }
            EnumVariantFields::Unnamed(types) => {
                let mut lhs_field_variable_names = Vec::new();
                let mut rhs_field_variable_names = Vec::new();
                for i in 0..types.len() {
                    lhs_field_variable_names.push(syn::Ident::new(&format!("lhs_f{}", i), name.span()));
                    rhs_field_variable_names.push(syn::Ident::new(&format!("rhs_f{}", i), name.span()));
                }
                let lhs_fields = quote! {
                    #( #lhs_field_variable_names, )*
                };
                let rhs_fields = quote! {
                    #( #rhs_field_variable_names, )*
                };
                let lhs_last_field = lhs_field_variable_names.pop().unwrap();
                let rhs_last_field = rhs_field_variable_names.pop().unwrap();
                let gen = quote! {
                    (#name::#variant(#lhs_fields), #name::#variant(#rhs_fields)) => {
                        #( #lhs_field_variable_names == #rhs_field_variable_names && )*
                        #lhs_last_field == #rhs_last_field
                    }
                };
                eq_vec.push(gen);
            },
            EnumVariantFields::Named(types, names) => {
                let mut lhs_field_variable_names = Vec::new();
                let mut rhs_field_variable_names = Vec::new();
                for i in 0..types.len() {
                    lhs_field_variable_names.push(syn::Ident::new(&format!("lhs_f{}", i), name.span()));
                    rhs_field_variable_names.push(syn::Ident::new(&format!("rhs_f{}", i), name.span()));
                }
                let lhs_fields = quote! {
                    #( #names: #lhs_field_variable_names, )*
                };
                let rhs_fields = quote! {
                    #( #names: #rhs_field_variable_names, )*
                };
                let lhs_last_field = lhs_field_variable_names.pop().unwrap();
                let rhs_last_field = rhs_field_variable_names.pop().unwrap();
                let gen = quote! {
                    (#name::#variant{#lhs_fields}, #name::#variant{#rhs_fields}) => {
                        #( #lhs_field_variable_names == #rhs_field_variable_names && )*
                        #lhs_last_field == #rhs_last_field
                    }
                };
                eq_vec.push(gen);
            }
        }
    }

    let gen = quote! {
        impl Clone for #name {
            fn clone(&self) -> Self 
            {
                *self
            }
        }

        impl PartialEq for #name {
            fn eq(&self, other: &Self) -> bool 
            {
                match (self, other) {
                    #( #eq_vec, )*
                    (_, _) => false,
                }
            }
        }

        #eq_and_clone_specs
    };

    gen
}

fn generate_clone_and_eq_proofs_for_union(
    name: &syn::Ident,
    idents: &Vec<syn::Ident>,
) -> proc_macro2::TokenStream {
    let eq_and_clone_spec = generate_eq_and_clone_specs(&name);

    let gen = quote! {
        impl Clone for #name {
            fn clone(&self) -> Self 
            {
                *self
            }
        }

        impl PartialEq for #name {
            fn eq(&self, other: &Self) -> bool 
            {
                unsafe {
                    match (self, other) {
                        #( (#name { #idents: val0 }, # name { #idents: val1 }) => val0 == val1, )*
                        (_, _) => false
                    }
                }
            }
        }

        #eq_and_clone_spec
    };

    gen
}

fn generate_eq_and_clone_specs(name: &syn::Ident) -> proc_macro2::TokenStream {
    let clone_spec_name = syn::Ident::new(&format!("ex_{}_clone", name.to_string().to_lowercase()), name.span());
    let eq_spec_name = syn::Ident::new(&format!("ex_{}_eq", name.to_string().to_lowercase()), name.span());

    let gen = quote! {
        impl Eq for #name {}

        ::builtin_macros::verus!{
            #[verifier::external_fn_specification]
            pub fn #clone_spec_name(b: &#name) -> (res: #name)
                ensures
                    *b == res
            {
                b.clone()
            }

            #[verifier::external_fn_specification]
            pub fn #eq_spec_name(lhs: &#name, rhs: &#name) -> (b: bool)
                ensures 
                    b == (lhs == rhs)
            {
                lhs.eq(rhs)    
            }

            impl CloneProof for #name 
            {
                fn clone_provable(&self) -> (res: #name)
                    ensures
                        *self == res
                {
                    self.clone()
                }
            }

            impl EqProof for #name 
            {
                fn eq_provable(&self, other: &Self) -> (b: bool) 
                    ensures 
                        b == (self == other)
                {
                    self.eq(other)
                }
            }
        }
    };

    gen
}

// Alignment is the same as size on x86. 
// NOTE: prior to Rust 1.77, i128/u128 alignment
// was 8 bytes. 
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
                fn clone_provable(&self) -> (res: #ty)
                    ensures
                        *self == res
                {
                    self.clone()
                }
            }

            impl EqProof for #ty 
            {
                fn eq_provable(&self, other: &Self) -> (b: bool) 
                    ensures 
                        b == (self == other)
                {
                    self == other
                }
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
