#![cfg_attr(verus_keep_ghost, verus::trusted)]
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::power_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;

verus! {

pub trait SimpleCheckPermission<State> : Sized
{
    spec fn permits(&self, s: State) -> bool;
    spec fn id(&self) -> int;

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<State>, new_state: State)
        requires
            self.id() == old(r).id(),
            self.permits(new_state),
        ensures
            r.id() == old(r).id(),
            r@ == new_state
        opens_invariants
            any;
}

pub struct SimplePermissionAdapter<State, SimplePerm>
    where
        SimplePerm: SimpleCheckPermission<State>
{
    perm: SimplePerm,
    _state: core::marker::PhantomData<State>,
}

impl<State, SimplePerm> SimplePermissionAdapter<State, SimplePerm>
    where
        SimplePerm: SimpleCheckPermission<State>
{
    proof fn new(tracked perm: SimplePerm) -> (tracked result: Self)
        ensures
            result.id() == perm.id(),
            forall |s1, s2| perm.permits(s2) <==> result.permits(s1, s2),
    {
        Self{
            perm: perm,
            _state: core::marker::PhantomData,
        }
    }
}

impl<State, SimplePerm> CheckPermission<State> for SimplePermissionAdapter<State, SimplePerm>
    where
        SimplePerm: SimpleCheckPermission<State>
{
    type Completion = ();

    closed spec fn permits(&self, s1: State, s2: State) -> bool {
        self.perm.permits(s2)
    }

    closed spec fn id(&self) -> int {
        self.perm.id()
    }

    closed spec fn completed(&self, c: Self::Completion) -> bool {
        true
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<State>, new_state: State) -> (tracked result: Self::Completion) {
        self.perm.apply(credit, r, new_state);
        ()
    }
}

pub trait PermissionFactory<State>: Sized
{
    type Perm: CheckPermission<State>;

    spec fn permits(&self, s1: State, s2: State) -> bool;
    spec fn id(&self) -> int;

    proof fn grant_permission(tracked &self) -> (tracked perm: Self::Perm)
        ensures
            self.id() == perm.id(),
            forall|s1, s2| self.permits(s1, s2) ==> #[trigger] perm.permits(s1, s2);

    proof fn clone(tracked &self) -> (tracked other: Self)
        ensures
            self.id() == other.id(),
            forall|s1, s2| self.permits(s1, s2) ==> #[trigger] other.permits(s1, s2);
}

pub struct CombinedPermission<State, PermA, PermB>
    where
        PermA: CheckPermission<State>,
        PermB: CheckPermission<State>,
{
    a: PermA,
    b: PermB,
    _s: core::marker::PhantomData<State>,
}

impl<State, PermA, PermB> CombinedPermission<State, PermA, PermB>
    where
        PermA: CheckPermission<State>,
        PermB: CheckPermission<State>,
{
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.a.id() == self.b.id()
    }

    pub proof fn new(tracked a: PermA, tracked b: PermB) -> (tracked combined: Self)
        requires
            a.id() == b.id(),
        ensures
            combined.id() == a.id(),
            forall|s1: State, s2: State| #[trigger] combined.permits(s1, s2) <==>
                a.permits(s1, s2) || b.permits(s1, s2)
    {
        Self{
            a: a,
            b: b,
            _s: core::marker::PhantomData,
        }
    }
}

impl<State, PermA, PermB> CheckPermission<State> for CombinedPermission<State, PermA, PermB>
    where
        PermA: CheckPermission<State>,
        PermB: CheckPermission<State>,
{
    type Completion = ();

    closed spec fn permits(&self, s1: State, s2: State) -> bool {
        self.a.permits(s1, s2) || self.b.permits(s1, s2)
    }

    closed spec fn id(&self) -> int {
        self.a.id()
    }

    closed spec fn completed(&self, c: Self::Completion) -> bool {
        true
    }

    proof fn apply(tracked self, tracked credit: OpenInvariantCredit, tracked r: &mut GhostVarAuth<State>, new_state: State) -> (tracked result: Self::Completion) {
        use_type_invariant(&self);
        if self.a.permits(r@, new_state) {
            self.a.apply(credit, r, new_state);
        } else {
            self.b.apply(credit, r, new_state);
        }
        ()
    }
}

#[allow(dead_code)]
pub struct PoWERPersistentMemoryRegion<PMRegion>
    where
        PMRegion: PersistentMemoryRegion
{
    pm_region: PersistentMemoryRegionAtomic<PMRegion>,
}

impl<PMRegion> PoWERPersistentMemoryRegion<PMRegion>
    where
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

    #[inline(always)]
    #[verifier::atomic]
    pub exec fn agree(&self, Tracked(r): Tracked<&GhostVar<Seq<u8>>>)
        requires
            self.inv(),
            self.id() == r.id(),
        ensures
            self@.durable_state == r@,
        opens_invariants
            none
        no_unwind
    {
        self.pm_region.agree(Tracked(r));
    }

    pub exec fn new(pm_region: PMRegion) -> (result: (Self, Tracked<GhostVar<Seq<u8>>>))
        requires
            pm_region.inv(),
        ensures
            result.0.inv(),
            result.0@ == pm_region@,
            result.0.constants() == pm_region.constants(),
            result.1@.id() == result.0.id(),
            result.1@@ == result.0@.durable_state,
    {
        let (pm_region, Tracked(r)) = PersistentMemoryRegionAtomic::new(pm_region);
        let power_region = Self {
            pm_region: pm_region,
        };
        (power_region, Tracked(r))
    }

    pub exec fn new_atomic(pm_region: PersistentMemoryRegionAtomic<PMRegion>) -> (result: Self)
        requires
            pm_region.inv(),
        ensures
            result.inv(),
            result@ == pm_region@,
            result.constants() == pm_region.constants(),
            result.id() == pm_region.id(),
    {
        Self {
            pm_region: pm_region,
        }
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

    // This executable function performs a write, and it requires the
    // caller to supply permission authorizing that write. The caller
    // must prove that for every state this memory can crash and
    // recover into, the permission authorizes that state.
    #[allow(unused_variables)]
    pub exec fn write<Perm>(&mut self, addr: u64, bytes: &[u8], perm: Tracked<Perm>) -> (result: Tracked<Perm::Completion>)
        where
            Perm: CheckPermission<Seq<u8>>,
        requires
            old(self).inv(),
            perm@.id() == old(self).id(),
            addr + bytes@.len() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, bytes@)
                  ==> #[trigger] perm@.permits(old(self)@.durable_state, s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, bytes@),
            perm@.completed(result@),
    {
        self.pm_region.write(addr, bytes, perm)
    }

    // This executable function performs a write that serializes an
    // object of type `S`, and it requires the caller to supply
    // permission authorizing that write. The caller must prove that
    // for every state this memory can crash and recover into, the
    // permission authorizes that state.
    #[allow(unused_variables)]
    pub exec fn serialize_and_write<Perm, S>(&mut self, addr: u64, to_write: &S, perm: Tracked<Perm>) -> (result: Tracked<Perm::Completion>)
        where
            Perm: CheckPermission<Seq<u8>>,
            S: PmCopy + Sized
        requires
            old(self).inv(),
            perm@.id() == old(self).id(),
            addr + S::spec_size_of() <= old(self)@.len(),
            // The key thing the caller must prove is that all crash states are authorized by `perm`
            forall |s| can_result_from_partial_write(s, old(self)@.durable_state, addr as int, to_write.spec_to_bytes())
                  ==> #[trigger] perm@.permits(old(self)@.durable_state, s),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self.id() == old(self).id(),
            self@.can_result_from_write(old(self)@, addr as int, to_write.spec_to_bytes()),
            perm@.completed(result@),
    {
        self.pm_region.serialize_and_write(addr, to_write, perm)
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

}
