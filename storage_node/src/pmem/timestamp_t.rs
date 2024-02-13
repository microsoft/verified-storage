use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    pub struct PmTimestamp {
        pub value: int,
    }

    // we should only be able to get one PM timestamp per device?

    impl PmTimestamp {
        pub closed spec fn inc_timestamp(self) -> Self {
            Self {
                value: self.value + 1
            }
        }

        // pub closed spec fn timestamp_corresponds_to_regions<PMRegions: PersistentMemoryRegions>(&self, regions: &PMRegions) -> bool;
    }

    impl Clone for PmTimestamp {
        fn clone(&self) -> Self {
            Self {
                value: self.value
            }
        }
    }

}
