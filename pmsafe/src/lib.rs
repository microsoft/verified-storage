extern crate proc_macro;
use proc_macro::TokenStream;
use syn;
use quote::{quote, quote_spanned};

#[proc_macro_derive(PmSafe)]
pub fn derive_pmsafe(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    check_pmsafe(&ast)
}

fn check_pmsafe(ast: &syn::DeriveInput) -> TokenStream {
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
fn check_repr_c(name: &syn::Ident, attrs: &Vec<syn::Attribute>) ->  Result<(), TokenStream>  
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

fn check_types<'a>(name: &'a syn::Ident, data: &'a syn::Data) -> Result<Vec<&'a syn::Type>, TokenStream> 
{
    let mut type_vec = Vec::new();
    match data {
        syn::Data::Struct(data) => {
            let fields = &data.fields; 
            match fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let ty = &field.ty;
                        // check_field_type(ty)?;
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

// fn check_field_type(ty: &syn::Type) -> Result<(), TokenStream> {
//     match ty {
//         syn::Type::Path(path) => {
//             // valid path types: numeric types, booleans

//             // get_ident returns None if the path has any leading colons, more than one segment,
//             // or if the first segment has any angle bracket or paren path arguments. This excludes
//             // generic types, tuples, and qualified paths.
//             match path.path.get_ident() {
//                 Some(ident) => {
//                     Ok(())
//                     // if !LEGAL_TYPES.contains(&ident.to_string().as_str()) {
//                     //     let msg = format!("Only numeric types, booleans, and arrays are allowed in PmSafe structs");
//                     //     Err(syn::Error::new(ty.span(), &msg).into_compile_error().into())
//                     // } else {
//                     //     Ok(())
//                     // }
//                 }
//                 None => {
//                     let msg = format!("Only numeric types, booleans, and arrays are allowed in PmSafe structs");
//                     Err(syn::Error::new(ty.span(), &msg).into_compile_error().into())
//                 }
//             }
//         }
//         // TODO: double check
//         syn::Type::Array(array) => {
//             // An array [T; N] is legal as long as T is a legal primitive type
//             let elem_type = &array.elem;
//             check_field_type(elem_type)
//         }
//         _ => {
//             // all other types are always illegal
//             // TODO: more detailed/informative error message
//             let msg = format!("Only numeric types, booleans, and arrays are allowed in PmSafe structs");
//             return Err(syn::Error::new(ty.span(), &msg).into_compile_error().into())
//         }
//     }
// }
   
