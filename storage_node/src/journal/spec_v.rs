use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::{pmcopy_t::*, pmemspec_t::*, pmemutil_v::*, traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe}};
use crate::common::util_v::*;
use deps_hack::PmCopy;

verus! {

    pub struct JournalConstants {
        pub app_version_number: u64,
        pub app_program_guid: u128,
        pub app_static_area_start: u64,
        pub app_static_area_end: u64,
        pub app_dynamic_area_start: u64,
        pub app_dynamic_area_end: u64,
    }

    pub struct JournalState {
        pub constants: JournalConstants,
        pub abort: Seq<u8>,
        pub read: Seq<u8>,
        pub commit: Seq<u8>,
        pub journal_empty: bool,
        pub journaled_addrs: Set<int>,
    }

    pub enum JournalError {
        NotEnoughSpace,
        CRCError,
    }
    
}
