use crate::pmem::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
    #[derive(Eq, PartialEq)]
    #[verifier::ext_equal]
    pub struct PmTimestamp {
        value: int,
        device_id: int
    }

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

        pub closed spec fn value(&self) -> int
        {
            self.value
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

    pub proof fn lemma_auto_timestamp_helpers()
        ensures
            forall |ts: PmTimestamp| #[trigger] ts.inc_timestamp().value() == #[trigger] ts.value() + 1,
            forall |ts: PmTimestamp| #[trigger] ts.inc_timestamp().gt(ts),
            forall |ts: PmTimestamp| #[trigger] ts.inc_timestamp().device_id() == #[trigger] ts.device_id(),
            forall |t1: PmTimestamp, t2, t3| t1.gt(t2) && t2.gt(t3) ==> t1.gt(t3),
            forall |t1: PmTimestamp, t2: PmTimestamp| t1.value() == t2.value() && t1.device_id() == t2.device_id() <==> t1 == t2,
            forall |t1: PmTimestamp, t2: PmTimestamp, x: int|
                x > 0 && #[trigger] t1.value() == #[trigger] (t2.value() + x) ==> #[trigger] t1.gt(t2)
    {}

    /// Higher-level storage component modules (e.g., multilog) should implement this
    /// in order to be able to update their ghost timestamp when other components on
    /// the same device perform a global flush/fence.
    pub trait TimestampedModule : Sized {
        type RegionsView;

        spec fn get_timestamp(&self) -> PmTimestamp;

        // this function should invoke the `inv` function for internal PM regions
        spec fn inv(self) -> bool;

        // TODO: having this be an exec function seems wrong -- but I want to
        // use preconditions/postconditions, and not sure how else to update
        // ghost variable stored inside a concrete implementor...
        fn update_timestamp(&mut self, new_timestamp: Ghost<PmTimestamp>)
            requires
                old(self).inv(),
                new_timestamp@.gt(old(self).get_timestamp()),
                new_timestamp@.device_id() == old(self).get_timestamp().device_id()
            ensures
                self.inv(),
                self.get_timestamp() == new_timestamp;
    }
}
