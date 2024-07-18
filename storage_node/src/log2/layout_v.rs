use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::util_v::*;
use deps_hack::{PmSafe, PmSized};

verus! {

    // TODO: this should probably be given by the user/determined based on the size of log entry structs being appended
    pub const MIN_LOG_AREA_SIZE: u64 = 1;
    #[repr(C)]
    #[derive(PmSized, PmSafe, Copy, Clone, Default)]
    pub struct LogMetadata {
        pub log_length: u64,
        pub head: u128,
    }

    impl PmCopy for LogMetadata {}

}