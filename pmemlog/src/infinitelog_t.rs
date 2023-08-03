/*

  This file models the abstraction of an infinite log that our log
  implementation is supposed to implement.

*/

use crate::pmemspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set::*;

verus! {
    #[verifier::ext_equal]
    pub struct AbstractInfiniteLogState {
        pub head: int,
        pub log: Seq<u8>,
        pub capacity: int,
    }

    impl AbstractInfiniteLogState {
        pub open spec fn initialize(capacity: int) -> Self {
            Self{ head: 0int, log: Seq::<u8>::empty(), capacity: capacity }
        }

        pub open spec fn append(self, bytes: Seq<u8>) -> Self {
            Self{ head: self.head, log: self.log + bytes, capacity: self.capacity }
        }

        pub open spec fn advance_head(self, new_head: int) -> Self
        {
            if self.head <= new_head <= self.head + self.log.len() {
                let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
                Self{ head: new_head, log: new_log, capacity: self.capacity }
            }
            else {
                self
            }
        }
    }

}
