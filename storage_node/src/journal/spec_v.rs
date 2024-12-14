use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::util_v::*;
use deps_hack::PmCopy;

verus! {

    pub struct JournalState {
        pub abort: Seq<u8>,
        pub read: Seq<u8>,
        pub commit: Seq<u8>,
        pub journaled_addrs: Set<int>,
    }

    pub enum JournalError {
        NotEnoughSpace,
        CRCError,
    }

    pub const APP_AREA_ALIGNMENT: u64 = 16;
    
}
