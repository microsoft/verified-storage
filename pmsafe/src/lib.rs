//! This crate defines three proc macros to derive PM-safety-related
//! traits:
//! - PmSafe, a marker trait indicating whether a structure is safe 
//!   to write to PM
//! - PmSized, a trait that helps calculate the size of structures
//!   so they can be safely read from PM
//! - Plus several related auxiliary traits that help us work around
//!   limitations in Verus and Rust.
//! The macros themselves are documented in pmsafe_macros.rs.

extern crate proc_macro;
use proc_macro::TokenStream;

use crate::pmsafe_macros::*;

mod pmsafe_macros;

// #[proc_macro_derive(PmSafe)]
// pub fn derive_pmsafe(input: TokenStream) -> TokenStream {
//     let ast: syn::DeriveInput = syn::parse(input).unwrap();
//     check_pmsafe(&ast)
// }

// #[proc_macro_derive(PmSized)]
// pub fn pmsized(input: TokenStream) -> TokenStream {
//     let ast: syn::DeriveInput = syn::parse(input).unwrap();
//     generate_pmsized(&ast)
// }

#[proc_macro_derive(PmCopy)]
pub fn pmcopy(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    generate_pmcopy(&ast)
}

#[proc_macro]
pub fn pmsized_primitive(input: TokenStream) -> TokenStream {
    let ty: syn::Type = syn::parse(input).unwrap();
    generate_pmsized_primitive(&ty)
}