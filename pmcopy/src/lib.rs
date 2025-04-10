//! This crate defines two proc macros to help with PM-safety-related
//! traits:
//! - A derive macro for PmCopy that also implements PmSafe, PmSized-related
//!   traits, and several methods/functions to make it easier to reason
//!   about cloning PmCopy objects. 
//! - pmcopy_primitive, a function-like macro that generates PmCopy-related
//!   code for primitive types (since PmCopy cannot be derived for these types)
//! The macros themselves are documented in pmcopy_macros.rs.

extern crate proc_macro;
use proc_macro::TokenStream;

use crate::pmcopy_macros::*;

mod pmcopy_macros;

#[proc_macro_derive(PmCopy)]
pub fn pmcopy(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    generate_pmcopy(&ast)
}

#[proc_macro]
pub fn pmcopy_primitive(input: TokenStream) -> TokenStream {
    let ty: syn::Type = syn::parse(input).unwrap();
    generate_pmcopy_primitive(&ty)
}