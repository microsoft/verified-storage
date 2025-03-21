#![feature(maybe_uninit_as_bytes)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_write_slice)]

#![allow(unused_imports)]
#![allow(unused_braces)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(dead_code)]
#![allow(unused_mut)]

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

pub mod common;
pub mod journal;
pub mod kv2;
// pub mod log;
// pub mod multilog;
pub mod pmem;
pub mod testkv_v;

use testkv_v::*;

mod tests {

use super::*;

// #[test]
// fn check_multilog_in_volatile_memory() {
//     assert!(test_multilog_in_volatile_memory());
// }

//#[test]
//fn check_durable_on_memory_mapped_file () {
//    test_durable_on_memory_mapped_file();
//}

#[test]
fn check_kv_on_memory_mapped_file () -> Result<(), ()>
{
    test_kv_on_memory_mapped_file()
}

#[test]
fn check_kv_on_concurrent_memory_mapped_file () -> Result<(), ()>
{
    test_concurrent_kv_on_memory_mapped_file()
}
    
}

verus! {

#[allow(dead_code)]
fn main()
{
    // test_multilog_in_volatile_memory();
    // test_multilog_on_memory_mapped_file();
    // test_log_on_memory_mapped_file();
    // test_durable_on_memory_mapped_file();
    let _ = test_kv_on_memory_mapped_file();
    let _ = test_concurrent_kv_on_memory_mapped_file();
}

}
