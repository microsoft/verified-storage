use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    #[derive(PartialEq, Eq)]
    pub struct PmTimestamp {
        pub value: int,
    }

    // TODO: should this be tracked? if so, might need to implement clone?
    impl PmTimestamp {
        pub closed spec fn inc_timestamp(self) -> Self {
            Self {
                value: self.value + 1
            }
        }
    }

    impl SpecOrd for PmTimestamp {
        fn spec_lt(self, rhs: PmTimestamp) -> bool {
            self.value < rhs.value
        }

        fn spec_le(self, rhs: PmTimestamp) -> bool {
            self.value <= rhs.value
        }

        fn spec_gt(self, rhs: PmTimestamp) -> bool {
            self.value > rhs.value
        }

        fn spec_ge(self, rhs: PmTimestamp) -> bool {
            self.value >= rhs.value
        }
    }
}
