use proc_macro::TokenStream;
use syn::{self, spanned::Spanned};
use quote::{quote, quote_spanned, format_ident};

pub fn check_pmsafe(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let attrs = &ast.attrs;
    if let Err(e) = check_repr_c(name, attrs) {
        return e;
    }

    let data = &ast.data;
    let mut types = match check_types(name, data) {
        Ok(types) => types,
        Err(e) => return e,
    };
    // not strictly necessary, but makes the expanded macro look nicer
    types.dedup();

    let gen = quote! {
        unsafe impl PmSafe for #name 
            where 
            #( #types: PmSafe, )*
        {}
    };
    gen.into()
}

// This function checks whether the struct has the repr(C) attribute so that we can
// trigger a compiler error if it doesn't. The repr(C) attribute ensures that the 
// structure has a consistent layout in memory, which is necessary to specify 
// serialization correctly.
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

pub fn check_types<'a>(name: &'a syn::Ident, data: &'a syn::Data) -> Result<Vec<&'a syn::Type>, TokenStream> 
{
    let mut type_vec = Vec::new();
    match data {
        syn::Data::Struct(data) => {
            let fields = &data.fields; 
            match fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let ty = &field.ty;
                        type_vec.push(ty);
                    }
                    Ok(type_vec)
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

pub fn generate_pmsized(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
   
    // PmSized structures must be repr(C), or the size calculation 
    // will not be correct
    let attrs = &ast.attrs;
    if let Err(e) = check_repr_c(name, attrs) {
        return e;
    }

    let data = &ast.data;
    let mut types = match check_types(name, data) {
        Ok(types) => types,
        Err(e) => return e,
    };

    // let get_size_fn = syn::Ident::new(&format!("get_size_of_{}", name.to_string().to_lowercase()), name.span());
    // let get_align_fn = syn::Ident::new(&format!("get_align_of_{}", name.to_string().to_lowercase()), name.span());

    let mut exec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: usize = offset + <#ty>::size_of() + padding_needed(offset, <#ty>::align_of()); 
        };
        exec_tokens_vec.push(new_tokens);
    }

    let mut spec_tokens_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            let offset: ::builtin::int = offset + <#ty>::spec_size_of() + spec_padding_needed(offset, <#ty>::spec_align_of()); 
        };
        spec_tokens_vec.push(new_tokens);
    }

    let mut exec_align_vec = Vec::new();
    for ty in types.iter() {
        let new_tokens = quote! {
            // assert(align_seq[i] == <#ty>::spec_align_of());
            // let ghost old_largest: usize = largest_alignment;
            if largest_alignment <= <#ty>::align_of() {
                largest_alignment = <#ty>::align_of();
            }
            // assert(largest_alignment >= old_largest);
            // assert(largest_alignment as int >= align_seq[i]);
            // let ghost i = i + 1;
            // assert forall |j: int| 0 <= j < i implies largest_alignment as int >= align_seq[j] by {};
            
        };
        exec_align_vec.push(new_tokens);
    }

    let spec_alignment = quote! {
        let alignment_seq = seq![#(<#types>::spec_align_of(),)*];
        alignment_seq.max()
    };

    
    let const_name = syn::Ident::new(&format!("SIZE_CHECK_{}", name.to_string().to_uppercase()), name.span());


    let gen = quote! {
    //     ::builtin_macros::verus!(

    //     impl SpecPmSized for #name {
    //         open spec fn spec_size_of() -> ::builtin::int 
    //         {
    //             let offset: ::builtin::int = 0;
    //             #( #spec_tokens_vec )*
    //             offset
    //         }      

    //         open spec fn spec_align_of() -> ::builtin::int 
    //         {
    //             #spec_alignment
    //         }
    //     }

        
    // );

    // impl const PmSized for #name {
    //     // #[verifier::external_body]
    //     const SIZE_CHECK: usize = (core::mem::size_of::<#name>() == <#name>::size_of()) as usize - 1;

    //     fn size_of() -> usize 
    //     {
    //         let offset: usize = 0;
    //         #( #exec_tokens_vec )*
    //         offset
    //     }

    //     fn align_of() -> usize {
    //         let mut largest_alignment: usize = 0;
    //         // let ghost align_seq = seq![#(<#types>::spec_align_of(),)*];
    //         // assert(align_seq.max() == Self::spec_align_of());
    //         // let ghost i: int = 0;
    //         #( #exec_align_vec )*
    //         // assert(i == align_seq.len());
    //         // assert forall |j: int| 0 <= j < align_seq.len() implies largest_alignment as int >= align_seq[j] by {};
    //         // proof {
    //         //     align_seq.max_ensures();
    //         // }
    //         // assert(largest_alignment == align_seq.max());
    //         largest_alignment
    //     }
    // }

    };
    gen.into()
}

const BOOL_SIZE: usize = 1;
const CHAR_SIZE: usize = 4;
const I8_SIZE: usize = 1;
const I16_SIZE: usize = 2;
const I32_SIZE: usize = 4;
const I64_SIZE: usize = 8;
const I128_SIZE: usize = 16;
const ISIZE_SIZE: usize = 8;
const U8_SIZE: usize = 1;
const U16_SIZE: usize = 2;
const U32_SIZE: usize = 4;
const U64_SIZE: usize = 8;
const U128_SIZE: usize = 16;
const USIZE_SIZE: usize = 8;

// const SIZE_CHECK: usize = (core::mem::size_of::<u8>() == 16) as usize - 1;


pub fn generate_pmsized_primitive(ty: &syn::Type) -> TokenStream {
    let (size, ty_name) = match ty {
        syn::Type::Path(type_path) => {
            match type_path.path.get_ident() {
                Some(ident) => {
                    let ty_name = ident.to_string();
                    let out = match ty_name.as_str() {
                        "bool" => BOOL_SIZE,
                        "char" => CHAR_SIZE,
                        "i8" => I8_SIZE,
                        "i16" => I16_SIZE,
                        "i32" => I32_SIZE,
                        "i64" => I64_SIZE,
                        "i128" => I128_SIZE,
                        "isize" => ISIZE_SIZE,
                        "u8" => U8_SIZE,
                        "u16" => U16_SIZE,
                        "u32" => U32_SIZE,
                        "u64" => U64_SIZE,
                        "u128" => U128_SIZE,
                        "usize" => USIZE_SIZE,
                        _ => {
                            return quote_spanned! {
                                ty.span() =>
                                compile_error!("pmsized_primitive can only be used on primitive types");
                            }.into()
                        }
                        
                    };
                    (out, ty_name)
                }
                None => return quote_spanned! {
                    ty.span() =>
                    compile_error!("pmsized_primitive can only be used on primitive types");
                }.into()
            }
        }
        _ => return quote_spanned! {
            ty.span() =>
            compile_error!("pmsized_primitive can only be used on primitive types");
        }.into()
    };

    // let const_name = format_ident!("SIZE_CHECK_{}", ty);
    // let get_size_fn = syn::Ident::new(&format!("get_size_of_{}", ty_name.to_string().to_lowercase()), ty.span());
    // let get_align_fn = syn::Ident::new(&format!("get_align_of_{}", ty_name.to_string().to_lowercase()), ty.span());
    let const_name = syn::Ident::new(&format!("SIZE_CHECK_{}", ty_name.to_string().to_uppercase()), ty.span());

    let gen = quote!{
        ::builtin_macros::verus!(
            impl SpecPmSized for #ty {
                open spec fn spec_size_of() -> ::builtin::int { #size as ::builtin::int }
                open spec fn spec_align_of() -> ::builtin::int { #size as ::builtin::int }
            }
        );

        impl const PmSized for #ty {
            // #[verifier::external_body]
            const SIZE_CHECK: usize = (core::mem::size_of::<#ty>() == <#ty>::size_of()) as usize - 1;
            fn size_of() -> usize { #size }
            fn align_of() -> usize { #size }
        }
    };
    gen.into()
}

// Try adding the ipmls back in and then derive/macro them in one  by one to figure out where 
// the hell this issue is happening? Might have to only build the pmem module and take out some
// files for that to work...