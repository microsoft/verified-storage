//! This file contains a logical-atomicity-style specification for how
//! a persistent memory region behaves, and a wrapper that transforms
//! a PersistentMemoryRegion into a region with a logatom-style spec.
//!
//! Even though the specification is logically-atomic, the API expects
//! there to be at most writer at a time; no write-write or read-write
//! concurrency is allowed.  The logically-atomic specification is used
//! to capture the possible crash states at any point in the execution.

// #![verus::trusted]
use crate::pmem::pmemspec_t::*;
use crate::pmem::frac_v::Frac;
use crate::pmem::logatom_v::{MutOperation, MutLinearizer};
use crate::pmem::pmcopy_t::*;
use vstd::prelude::*;

verus! {
    pub struct Write {
        pub id: int,
        pub addr: u64,
        pub bytes: Seq<u8>,
    }

    impl MutOperation for Write {
        type Resource = Frac<PersistentMemoryRegionView>;
        type ExecResult = ();
        type NewState = PersistentMemoryRegionView;

        open spec fn requires(self, pre: Self::Resource, new_state: Self::NewState, e: Self::ExecResult) -> bool {
            &&& pre.valid(self.id, 1)
            &&& new_state.can_result_from_write(pre@, self.addr as int, self.bytes)
        }

        open spec fn ensures(self, pre: Self::Resource, post: Self::Resource, new_state: Self::NewState) -> bool {
            &&& post.valid(self.id, 1)
            &&& post@ == new_state
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            r.valid(self.id, 1)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            self.addr + self.bytes.len() <= r@.len()
        }
    }

    pub struct PMRegionLA<PM: PersistentMemoryRegion> {
        pub pm: PM,
        pub res: Tracked<Frac<PersistentMemoryRegionView>>,
    }

    impl<PM: PersistentMemoryRegion> PMRegionLA<PM> {
        pub open spec fn inv(self) -> bool {
            &&& self.pm.inv()
            &&& self.pm@ == self.res@@
            &&& self.res@.valid(self.id(), 1)
        }

        pub closed spec fn id(self) -> int {
            self.res@.id()
        }

        pub open spec fn view(self) -> PersistentMemoryRegionView {
            self.res@@
        }

        pub open spec fn constants(self) -> PersistentMemoryConstants {
            self.pm.constants()
        }

        pub exec fn new(pm: PM) -> (result: (Self, Tracked<Frac<PersistentMemoryRegionView>>))
            requires
                pm.inv(),
            ensures
                result.0.inv(),
                result.0.constants() == pm.constants(),
                result.1@.valid(result.0.id(), 1),
                result.1@@ == pm@,
        {
            let tracked r = Frac::new(pm@);
            let pm_la = Self{
                pm: pm,
                res: Tracked(r.split(1)),
            };

            (pm_la, Tracked(r))
        }

        pub exec fn write<Lin>(&mut self, addr: u64, bytes: &[u8], Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::Completion>)
            where
                Lin: MutLinearizer<Write>,
            requires
                old(self).inv(),
                lin.pre(Write{ id: old(self).id(), addr: addr, bytes: bytes@ }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, bytes@),
                lin.post(Write{ id: old(self).id(), addr: addr, bytes: bytes@ }, (), result@),
        {
            let ghost op = Write{ id: old(self).id(), addr: addr, bytes: bytes@ };
            proof {
                lin.peek(op, self.res.borrow());
            }
            self.pm.write(addr, bytes);
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow_mut(), self.pm@, &());
            }
            Tracked(complete)
        }

        pub exec fn serialize_and_write<S, Lin>(&mut self, addr: u64, to_write: &S, Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::Completion>)
            where
                S: PmCopy + Sized,
                Lin: MutLinearizer<Write>,
            requires
                old(self).inv(),
                lin.pre(Write{ id: old(self).id(), addr: addr, bytes: to_write.spec_to_bytes() }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.constants() == old(self).constants(),
                self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
                lin.post(Write{ id: old(self).id(), addr: addr, bytes: to_write.spec_to_bytes() }, (), result@),
        {
            broadcast use pmcopy_axioms;

            let ghost op = Write{ id: old(self).id(), addr: addr, bytes: to_write.spec_to_bytes() };
            proof {
                lin.peek(op, self.res.borrow());
            }
            self.pm.serialize_and_write(addr, to_write);
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow_mut(), self.pm@, &());
            }
            Tracked(complete)
        }

        pub exec fn flush(&mut self)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.constants() == old(self).constants(),
                self@ == old(self)@,
                self@.flush_predicted(),
        {
            self.pm.flush()
        }
    }
}
