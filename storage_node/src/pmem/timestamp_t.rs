use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    // #[derive(PartialEq, Eq)]
    pub struct PmTimestamp {
        value: int,
        device_id: int
    }

    // TODO: should this be tracked? if so, might need to implement clone?
    impl PmTimestamp {
        pub closed spec fn new(device_id: int) -> Self
        {
            Self {
                value: 0,
                device_id,
            }
        }

        pub closed spec fn device_id(&self) -> int
        {
            self.device_id
        }

        pub closed spec fn inc_timestamp(self) -> Self {
            Self {
                value: self.value + 1,
                device_id: self.device_id
            }
        }

        pub closed spec fn lt(self, rhs: Self) -> bool {
            self.value < rhs.value
        }

        pub closed spec fn gt(self, rhs: Self) -> bool {
            self.value > rhs.value
        }
    }

    pub proof fn lemma_auto_timestamp_gt_transitive()
        ensures
            forall |t1: PmTimestamp, t2, t3| t1.gt(t2) && t2.gt(t3) ==> t1.gt(t3)
    {}

    // // this does not seem to be doing what you would like it to
    // impl SpecOrd for PmTimestamp {
    //     fn spec_lt(self, rhs: PmTimestamp) -> bool {
    //         self.value < rhs.value
    //     }

    //     fn spec_le(self, rhs: PmTimestamp) -> bool {
    //         self.value <= rhs.value
    //     }

    //     fn spec_gt(self, rhs: PmTimestamp) -> bool {
    //         self.value > rhs.value
    //     }

    //     fn spec_ge(self, rhs: PmTimestamp) -> bool {
    //         self.value >= rhs.value
    //     }
    // }
}
