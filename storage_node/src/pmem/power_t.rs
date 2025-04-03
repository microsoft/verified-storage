// #![verus::trusted]
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;

pub use crate::pmem::power_v::PoWERPersistentMemoryRegion;

verus! {

pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
    spec fn valid(&self, id: int) -> bool;

    proof fn apply(tracked &self, tracked credit: OpenInvariantCredit, tracked r: &mut Frac<State>, new_state: State)
        requires
            self.valid(old(r).id()),
            old(r).valid(old(r).id(), 1),
            self.check_permission(new_state),
        ensures
            r.id() == old(r).id(),
            r.valid(r.id(), 1),
            r@ == new_state
        opens_invariants
            any;
}

// PersistentMemoryRegionAtomic wraps a PersistentMemoryRegion in a logically-atomic
// style specification with a ghost resource, which can be used to reason about
// possible crash states using an atomic invariant.  This enforces the soundness
// of the PoWER interface defined in power_v.rs.
pub struct PersistentMemoryRegionAtomic<PM: PersistentMemoryRegion> {
    pub pm: PM,
    pub res: Tracked<Frac<Seq<u8>>>,
}

impl<PM: PersistentMemoryRegion> PersistentMemoryRegionAtomic<PM> {
    pub open spec fn inv(self) -> bool {
        &&& self.pm.inv()
        &&& self.pm@.durable_state == self.res@@
        &&& self.res@.valid(self.id(), 1)
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

    pub exec fn new(pm: PM) -> (result: (Self, Tracked<Frac<Seq<u8>>>))
        requires
            pm.inv(),
        ensures
            result.0.inv(),
            result.0.constants() == pm.constants(),
            result.0@ == pm@,
            result.1@.valid(result.0.id(), 1),
            result.1@@ == pm@.durable_state,
    {
        let tracked r = Frac::new(pm@.durable_state);
        let pm_la = Self{
            pm: pm,
            res: Tracked(r.split(1)),
        };

        (pm_la, Tracked(r))
    }

    pub exec fn write<Perm>(&mut self, addr: u64, bytes: &[u8], Tracked(perm): Tracked<&Perm>)
        where
            Perm: CheckPermission<Seq<u8>>
        requires
            old(self).inv(),
            addr + bytes@.len() <= old(self)@.len(),
            perm.valid(old(self).id()),
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, bytes@)
                    ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self.id() == old(self).id(),
            self.constants() == old(self).constants(),
            self@.can_result_from_write(old(self)@, addr as int, bytes@),
    {
        self.pm.write(addr, bytes);
        let credit = create_open_invariant_credit();
        proof {
            perm.apply(credit.get(), self.res.borrow_mut(), self.pm@.durable_state);
        }
    }

    pub exec fn serialize_and_write<S, Perm>(&mut self, addr: u64, to_write: &S, Tracked(perm): Tracked<&Perm>)
        where
            S: PmCopy + Sized,
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            addr + S::spec_size_of() <= old(self)@.len(),
            perm.valid(old(self).id()),
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, to_write.spec_to_bytes())
                    ==> #[trigger] perm.check_permission(s),
        ensures
            self.inv(),
            self.id() == old(self).id(),
            self.constants() == old(self).constants(),
            self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
    {
        broadcast use pmcopy_axioms;

        self.pm.serialize_and_write(addr, to_write);
        let credit = create_open_invariant_credit();
        proof {
            perm.apply(credit.get(), self.res.borrow_mut(), self.pm@.durable_state);
        }
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
