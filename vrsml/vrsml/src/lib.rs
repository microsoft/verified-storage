#![feature(maybe_uninit_as_bytes)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_write_slice)]

#![allow(unused_imports)]
#![allow(unused_braces)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(dead_code)]
#![allow(unused_mut)]

use vstd::prelude::*;

pub mod pmem;
pub mod spec_t;

use spec_t::*;

verus! {

fn main()
{
}

}
