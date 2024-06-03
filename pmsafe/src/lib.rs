extern crate proc_macro;
use proc_macro::TokenStream;

use crate::pmsafe_macros::*;

mod pmsafe_macros;

#[proc_macro_derive(PmSafe)]
pub fn derive_pmsafe(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    check_pmsafe(&ast)
}