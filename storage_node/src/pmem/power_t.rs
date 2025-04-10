#![cfg_attr(verus_keep_ghost, verus::trusted)]
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::pcm::frac::*;

pub use crate::pmem::power_v::{PoWERPersistentMemoryRegion, PermissionFactory};

verus! {

pub trait CheckPermission<State> : Sized
{
    type Completion;

    spec fn check_permission(&self, s1: State, s2: State) -> bool;
    spec fn id(&self) -> int;
    spec fn completed(&self, c: Self::Completion) -> bool;

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<State>, new_state: State) -> (tracked complete: Self::Completion)
        requires
            self.id() == old(r).id(),
            self.check_permission(old(r)@, new_state),
        ensures
            r.id() == old(r).id(),
            r@ == new_state,
            self.completed(complete),
        opens_invariants
            any;
}

// PersistentMemoryRegionAtomic wraps a PersistentMemoryRegion in a logically-atomic
// style specification with a ghost resource, which can be used to reason about
// possible crash states using an atomic invariant.  This enforces the soundness
// of the PoWER interface defined in power_v.rs.
pub struct PersistentMemoryRegionAtomic<PM: PersistentMemoryRegion> {
    pub pm: PM,
    pub res: Tracked<GhostVarAuth<Seq<u8>>>,
}

impl<PM: PersistentMemoryRegion> PersistentMemoryRegionAtomic<PM> {
    pub open spec fn inv(self) -> bool {
        &&& self.pm.inv()
        &&& self.pm@.durable_state == self.res@@
        &&& self.res@.id() == self.id()
    }

    pub closed spec fn id(self) -> int {
        self.res@.id()
    }

    pub open spec fn view(self) -> PersistentMemoryRegionView {
        self.pm@
    }

    pub open spec fn constants(self) -> PersistentMemoryConstants {
        self.pm.constants()
    }

    pub exec fn new(pm: PM) -> (result: (Self, Tracked<GhostVar<Seq<u8>>>))
        requires
            pm.inv(),
        ensures
            result.0.inv(),
            result.0.constants() == pm.constants(),
            result.0@ == pm@,
            result.1@.id() == result.0.id(),
            result.1@@ == pm@.durable_state,
    {
        let tracked (r_auth, r) = GhostVarAuth::new(pm@.durable_state);
        let pm_la = Self{
            pm: pm,
            res: Tracked(r_auth),
        };

        (pm_la, Tracked(r))
    }

    pub exec fn write<Perm>(&mut self, addr: u64, bytes: &[u8], Tracked(perm): Tracked<Perm>) -> (result: Tracked<Perm::Completion>)
        where
            Perm: CheckPermission<Seq<u8>>
        requires
            old(self).inv(),
            addr + bytes@.len() <= old(self)@.len(),
            perm.id() == old(self).id(),
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, bytes@)
                    ==> #[trigger] perm.check_permission(old(self)@.durable_state, s),
        ensures
            self.inv(),
            self.id() == old(self).id(),
            self.constants() == old(self).constants(),
            self@.can_result_from_write(old(self)@, addr as int, bytes@),
            perm.completed(result@),
    {
        self.pm.write(addr, bytes);
        let credit = create_open_invariant_credit();
        let tracked mut complete;
        proof {
            complete = perm.apply(credit.get(), self.res.borrow_mut(), self.pm@.durable_state);
        }
        Tracked(complete)
    }

    pub exec fn serialize_and_write<S, Perm>(&mut self, addr: u64, to_write: &S, Tracked(perm): Tracked<Perm>) -> (result: Tracked<Perm::Completion>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            perm.id() == old(self).id(),
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, to_write.spec_to_bytes())
                    ==> #[trigger] perm.check_permission(old(self)@.durable_state, s),
        ensures
            self.inv(),
            self.id() == old(self).id(),
            self.constants() == old(self).constants(),
            self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
            perm.completed(result@),
    {
        broadcast use pmcopy_axioms;

        self.pm.serialize_and_write(addr, to_write);
        let credit = create_open_invariant_credit();
        let tracked mut complete;
        proof {
            complete = perm.apply(credit.get(), self.res.borrow_mut(), self.pm@.durable_state);
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
