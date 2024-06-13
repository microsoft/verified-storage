extern crate proc_macro;
use proc_macro::TokenStream;

use crate::pmsafe_macros::*;

mod pmsafe_macros;

#[proc_macro_derive(PmSafe)]
pub fn derive_pmsafe(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    check_pmsafe(&ast)
}

#[proc_macro_derive(PmSized)]
pub fn pmsized(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    generate_pmsized(&ast)
}

#[proc_macro]
pub fn pmsized_primitive(input: TokenStream) -> TokenStream {
    let ty: syn::Type = syn::parse(input).unwrap();
    generate_pmsized_primitive(&ty)
}