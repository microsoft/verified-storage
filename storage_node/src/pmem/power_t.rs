// #![verus::trusted]
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::frac_v::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
    spec fn valid(&self, id: int) -> bool;

    proof fn apply(&self, tracked r: &mut Frac<State>, new_state: State)
        requires
            self.valid(old(r).id()),
            old(r).valid(old(r).id(), 1),
            self.check_permission(new_state),
        ensures
            r.id() == old(r).id(),
            r.valid(r.id(), 1),
            r@ == new_state;
}

#[allow(dead_code)]
pub struct PoWERPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pm_region: PMRegionLA<PMRegion>,
    perm: core::marker::PhantomData<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<Perm, PMRegion> PoWERPersistentMemoryRegion<Perm, PMRegion>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: PersistentMemoryRegion
{
    pub closed spec fn view(&self) -> PersistentMemoryRegionView
    {
        self.pm_region@
    }

    pub closed spec fn inv(&self) -> bool
    {
        self.pm_region.inv()
    }

    pub closed spec fn constants(&self) -> PersistentMemoryConstants
    {
        self.pm_region.constants()
    }

    pub closed spec fn id(&self) -> int
    {
        self.pm_region.id()
    }

    pub proof fn lemma_inv_implies_view_valid(&self)
        requires
            self.inv()
        ensures
            self@.valid(),
            self.constants().valid(),
    {
        self.pm_region.pm.lemma_inv_implies_view_valid();
    }

    pub exec fn new(pm_region: PMRegion) -> (result: (Self, Tracked<Frac<Seq<u8>>>))
        requires
            pm_region.inv(),
        ensures
            result.0.inv(),
            result.0@ == pm_region@,
            result.0.constants() == pm_region.constants(),
            result.1@.valid(result.0.id(), 1),
            result.1@@ == result.0@.durable_state,
    {
        let (pm_la, Tracked(r)) = PMRegionLA::new(pm_region);
        let power_region = Self {
            pm_region: pm_la,
            perm: core::marker::PhantomData,
        };
        (power_region, Tracked(r))
    }

    // This executable function returns an immutable reference to the
    // persistent memory region. This can be used to perform any
    // operation (e.g., read) that can't mutate the memory. After all,
    // this is a write-restricted memory, not a read-restricted one.
    pub exec fn get_pm_region_ref(&self) -> (pm_region: &PMRegion)
        requires
            self.inv(),
        ensures
            pm_region.inv(),
            pm_region@ == self@,
            pm_region.constants() == self.constants(),
    {
        &self.pm_region.pm
    }

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    #[allow(unused_variables)]
    pub exec fn write(&mut self, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            perm@.valid(old(self).id()),
            addr + bytes@.len() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, bytes@)
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, bytes@),
    {
        let ghost pmr = self.pm_region;
        self.pm_region.write(addr, bytes, perm);
    }

    #[allow(unused_variables)]
    pub exec fn serialize_and_write<S>(&mut self, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: PmCopy + Sized
        requires
            old(self).inv(),
            perm@.valid(old(self).id()),
            addr + S::spec_size_of() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, to_write.spec_to_bytes())
                  ==> #[trigger] perm@.check_permission(s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
    {
        self.pm_region.serialize_and_write(addr, to_write, perm);
    }

    // Even though the memory is write-restricted, no restrictions are
    // placed on calling `flush`. After all, `flush` can only narrow
    // the possible states the memory can crash into. So if the memory
    // is already restricted to only crash into good states, `flush`
    // automatically maintains that restriction.
    pub exec fn flush(&mut self)
        requires
            old(self).inv(),
        ensures
            old(self)@.flush_predicted(), // it must have been prophesized that this flush would happen
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@ == old(self)@,
    {
        self.pm_region.flush()
    }
}

// PMRegionLA wraps a PersistentMemoryRegion in a logically-atomic style with
// a ghost resource, which can be used to reason about possible crash states
// using an atomic invariant.  This enforces the soundness of the PoWER
// interface defined above.
pub struct PMRegionLA<PM: PersistentMemoryRegion> {
    pub pm: PM,
    pub res: Tracked<Frac<Seq<u8>>>,
}

impl<PM: PersistentMemoryRegion> PMRegionLA<PM> {
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
        proof {
            perm.apply(self.res.borrow_mut(), self.pm@.durable_state);
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
        proof {
            perm.apply(self.res.borrow_mut(), self.pm@.durable_state);
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
