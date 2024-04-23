use crate::pmem::wrpm_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    pub struct TrustedListPermission
    {
        // TODO: how many regions will this use? Probably just one?
        ghost is_state_allowable: spec_fn(Seq<Seq<u8>>) -> bool
    }

    impl CheckPermission<Seq<Seq<u8>>> for TrustedListPermission
    {
        closed spec fn check_permission(&self, state: Seq<Seq<u8>>) -> bool
        {
            (self.is_state_allowable)(state)
        }
    }
}
