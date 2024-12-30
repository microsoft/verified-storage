use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn opaque_mul(x: int, y: int) -> int
{
    x * y
}

#[verifier::opaque]
pub open spec fn opaque_div(x: int, y: int) -> int
    recommends
        y != 0
{
    x / y
}

}
