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
use crate::pmem::logatom_v::{ReadOperation, MutOperation, ReadLinearizer, MutLinearizer};
use crate::pmem::pmcopy_t::{PmCopy, PmCopyHelper, MaybeCorruptedBytes};
use vstd::prelude::*;

verus! {
    pub struct PMState {
        pub view: PersistentMemoryRegionView,
        pub constants: PersistentMemoryConstants,
    }

    pub struct GetRegionSize {
        pub id: int,
    }

    impl ReadOperation for GetRegionSize {
        type Resource = Frac<PMState>;
        type ExecResult = u64;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id, 1)
            &&& e == r@.view.len()
        }
    }

    pub struct ReadAligned<S: PmCopy + Sized> {
        pub id: int,
        pub addr: u64,
        pub _s: core::marker::PhantomData<S>,
    }

    impl<S: PmCopy + Sized> ReadOperation for ReadAligned<S> {
        type Resource = Frac<PMState>;
        type ExecResult = Result<MaybeCorruptedBytes<S>, PmemError>;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id, 1)
            &&& match e {
                Ok(bytes) => bytes_read_from_storage(bytes@,
                                                     r@.view.read_state.subrange(self.addr as int, self.addr + S::spec_size_of()),
                                                     self.addr as int,
                                                     r@.constants),
                _ => false,
            }
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            r.valid(self.id, 1)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            &&& self.addr + S::spec_size_of() <= r@.view.len()
            &&& S::bytes_parseable(r@.view.read_state.subrange(self.addr as int, self.addr + S::spec_size_of()))
        }
    }

    pub struct ReadUnaligned {
        pub id: int,
        pub addr: u64,
        pub num_bytes: u64,
    }

    impl ReadOperation for ReadUnaligned {
        type Resource = Frac<PMState>;
        type ExecResult = Result<Vec<u8>, PmemError>;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id, 1)
            &&& match e {
                Ok(bytes) => bytes_read_from_storage(bytes@,
                                                     r@.view.read_state.subrange(self.addr as int, self.addr + self.num_bytes as nat),
                                                     self.addr as int,
                                                     r@.constants),
                _ => false,
            }
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            r.valid(self.id, 1)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            self.addr + self.num_bytes <= r@.view.len()
        }
    }

    pub struct Write {
        pub id: int,
        pub addr: u64,
        pub bytes: Seq<u8>,
    }

    impl MutOperation for Write {
        type Resource = Frac<PMState>;
        type ExecResult = ();
        type NewState = PersistentMemoryRegionView;

        open spec fn requires(self, pre: Self::Resource, new_state: Self::NewState, e: Self::ExecResult) -> bool {
            &&& pre.valid(self.id, 1)
            &&& new_state.can_result_from_write(pre@.view, self.addr as int, self.bytes)
        }

        open spec fn ensures(self, pre: Self::Resource, post: Self::Resource, new_state: Self::NewState) -> bool {
            &&& post.valid(self.id, 1)
            &&& post@.constants == pre@.constants
            &&& post@.view == new_state
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            r.valid(self.id, 1)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            self.addr + self.bytes.len() <= r@.view.len()
        }
    }

    pub struct SerializeAndWrite<S: PmCopy + Sized> {
        pub id: int,
        pub addr: u64,
        pub to_write: S,
    }

    impl<S: PmCopy + Sized> MutOperation for SerializeAndWrite<S> {
        type Resource = Frac<PMState>;
        type ExecResult = ();
        type NewState = PersistentMemoryRegionView;

        open spec fn requires(self, pre: Self::Resource, new_state: Self::NewState, e: Self::ExecResult) -> bool {
            &&& pre.valid(self.id, 1)
            &&& new_state.can_result_from_write(pre@.view, self.addr as int, self.to_write.spec_to_bytes())
        }

        open spec fn ensures(self, pre: Self::Resource, post: Self::Resource, new_state: Self::NewState) -> bool {
            &&& post.valid(self.id, 1)
            &&& post@.constants == pre@.constants
            &&& post@.view == new_state
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            r.valid(self.id, 1)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            self.addr + S::spec_size_of() <= r@.view.len()
        }
    }

    pub struct Flush {
        pub id: int,
    }

    impl ReadOperation for Flush {
        type Resource = Frac<PMState>;
        type ExecResult = ();

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id, 1)
            &&& r@.view.flush_predicted()
        }
    }

    pub struct PMRegionLA<PM: PersistentMemoryRegion> {
        pm: PM,
        res: Tracked<Frac<PMState>>,
    }

    impl<PM: PersistentMemoryRegion> PMRegionLA<PM> {
        pub closed spec fn inv(self) -> bool {
            &&& self.pm.inv()
            &&& self.pm@ == self.res@@.view
            &&& self.pm.constants() == self.res@@.constants
            &&& self.res@.valid(self.id(), 1)
        }

        pub closed spec fn id(self) -> int {
            self.res@.id()
        }

        pub exec fn new(pm: PM) -> (result: (Self, Tracked<Frac<PMState>>))
            requires
                pm.inv(),
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id(), 1),
                result.1@@.view == pm@,
                result.1@@.constants == pm.constants(),
        {
            let ghost pm_state = PMState{
                view: pm@,
                constants: pm.constants(),
            };

            let tracked r = Frac::new(pm_state);
            let pm_la = Self{
                pm: pm,
                res: Tracked(r.split(1)),
            };

            (pm_la, Tracked(r))
        }

        pub exec fn get_region_size<Lin>(&self, Tracked(lin): Tracked<Lin>) -> (result: (u64, Tracked<Lin::Completion>))
            where
                Lin: ReadLinearizer<GetRegionSize>,
            requires
                self.inv(),
                lin.pre(GetRegionSize{ id: self.id() }),
            ensures
                lin.post(GetRegionSize{ id: self.id() }, result.0, result.1@),
        {
            let ghost op = GetRegionSize{ id: self.id() };
            let sz = self.pm.get_region_size();
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow(), &sz);
            }
            (sz, Tracked(complete))
        }

        pub exec fn read_aligned<S, Lin>(&self, addr: u64, Tracked(lin): Tracked<Lin>) -> (result: (Result<MaybeCorruptedBytes<S>, PmemError>, Tracked<Lin::Completion>))
            where
                S: PmCopy + Sized,
                Lin: ReadLinearizer<ReadAligned<S>>,
            requires
                self.inv(),
                lin.pre(ReadAligned{ id: self.id(), addr: addr, _s: core::marker::PhantomData }),
            ensures
                lin.post(ReadAligned{ id: self.id(), addr: addr, _s: core::marker::PhantomData }, result.0, result.1@),
        {
            let ghost op = ReadAligned{ id: self.id(), addr: addr, _s: core::marker::PhantomData };
            proof {
                lin.peek(op, self.res.borrow());
            }
            let bytes = self.pm.read_aligned(addr);
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow(), &bytes);
            }
            (bytes, Tracked(complete))
        }

        pub exec fn read_unaligned<Lin>(&self, addr: u64, num_bytes: u64, Tracked(lin): Tracked<Lin>) -> (result: (Result<Vec<u8>, PmemError>, Tracked<Lin::Completion>))
            where
                Lin: ReadLinearizer<ReadUnaligned>,
            requires
                self.inv(),
                lin.pre(ReadUnaligned{ id: self.id(), addr: addr, num_bytes: num_bytes }),
            ensures
                lin.post(ReadUnaligned{ id: self.id(), addr: addr, num_bytes: num_bytes }, result.0, result.1@),
        {
            let ghost op = ReadUnaligned{ id: self.id(), addr: addr, num_bytes: num_bytes };
            proof {
                lin.peek(op, self.res.borrow());
            }
            let bytes = self.pm.read_unaligned(addr, num_bytes);
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow(), &bytes);
            }
            (bytes, Tracked(complete))
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
                Lin: MutLinearizer<SerializeAndWrite<S>>,
            requires
                old(self).inv(),
                lin.pre(SerializeAndWrite{ id: old(self).id(), addr: addr, to_write: *to_write }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                lin.post(SerializeAndWrite{ id: old(self).id(), addr: addr, to_write: *to_write }, (), result@),
        {
            let ghost op = SerializeAndWrite{ id: old(self).id(), addr: addr, to_write: *to_write };
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

        pub exec fn flush<Lin>(&mut self, Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::Completion>)
            where
                Lin: ReadLinearizer<Flush>,
            requires
                old(self).inv(),
                lin.pre(Flush{ id: old(self).id() }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                lin.post(Flush{ id: old(self).id() }, (), result@),
        {
            let ghost op = Flush{ id: old(self).id() };
            let sz = self.pm.flush();
            let tracked mut complete;
            proof {
                complete = lin.apply(op, self.res.borrow(), &());
            }
            Tracked(complete)
        }
    }
}
