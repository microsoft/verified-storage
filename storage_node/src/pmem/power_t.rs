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

// Soundness argument for PoWER:
//
// Consider any predicate SoundnessParam::valid(state: Seq<u8>) that the
// application wants to enforce for possible crash states.  We construct
// an AtomicInvariant that holds the durable_state resource from
// PersistentMemoryRegionAtomic, and enforces SoundnessParam::valid() on it,
// while allowing the application to execute arbitrary code with access to
// a CheckPermission object that matches the application's valid() predicate.
//
// The soundness argument depends on invariant_recovery_soundness_axiom(),
// defined below, and the assumption that PersistentMemoryRegionAtomic soundly
// models crash behavior with respect to how the durable state resource is updated.

trait SoundnessParam<PM> : Sized
    where
        PM: PersistentMemoryRegion,
{
    // valid() captures the set of valid crash states that the application
    // may want to enforce using PoWER.
    spec fn valid(self, state: Seq<u8>) -> bool;

    // setup() is the executable function that implements the application's
    // initialization logic, setting up the contents of the persistent memory
    // region at first boot, and returning with the region satisfying valid().
    exec fn setup(&self, pm: &mut PM)
        requires
            old(pm).inv(),
        ensures
            pm.inv(),
            self.valid(pm@.durable_state);

    // recover() is the executable function that implements the application's
    // logic to recover after a crash, taking a PersistentMemoryRegionAtomic
    // that already satisfies valid(), and continuing to run until the next
    // crash.
    //
    // The application receives a permission `perm` that allows all crash
    // states specified by the soudness predicate's valid().
    exec fn recover<Perm>(&self, pm: PersistentMemoryRegionAtomic<PM>, Tracked(perm): Tracked<&Perm>)
        where
            Perm: CheckPermission<Seq<u8>>,
        requires
            pm.inv(),
            pm@.durable_state == pm@.read_state,
            perm.valid(pm.id()),
            forall |s| self.valid(s) ==> #[trigger] perm.check_permission(s),
            self.valid(pm@.durable_state);
}

// An example toy application modeled as SoundnessParam, to validate that
// it's possible to construct this trait.  The application enforces that
// location `addr` in persistent memory is always either `val0` or `val1`.

struct ExampleSoundnessApp {
    addr: u64,
    val0: u8,
    val1: u8,
}

impl<PM> SoundnessParam<PM> for ExampleSoundnessApp
    where
        PM: PersistentMemoryRegion,
{
    spec fn valid(self, state: Seq<u8>) -> bool {
        &&& self.addr < state.len()
        &&& {
            ||| state[self.addr as int] == self.val0
            ||| state[self.addr as int] == self.val1
        }
    }

    exec fn setup(&self, pm: &mut PM) {
        let len = pm.get_region_size();
        if self.addr >= len {
            loop {}
        }

        pm.write(self.addr, vec![self.val0].as_slice());
        pm.flush();
    }

    exec fn recover<Perm>(&self, pm: PersistentMemoryRegionAtomic<PM>, Tracked(perm): Tracked<&Perm>)
        where
            Perm: CheckPermission<Seq<u8>>,
    {
        let mut power_pm: PoWERPersistentMemoryRegion<Perm, PM> = PoWERPersistentMemoryRegion::new_atomic(pm);

        loop
            invariant
                power_pm.inv(),
                perm.valid(power_pm.id()),
                self.addr < power_pm@.len(),
                <Self as SoundnessParam<PM>>::valid(*self, power_pm@.durable_state),
                forall |s| <Self as SoundnessParam<PM>>::valid(*self, s) ==> #[trigger] perm.check_permission(s),
        {
            assert forall |s| can_result_from_partial_write(s, power_pm@.durable_state, self.addr as int, seq![self.val0]) implies #[trigger] perm.check_permission(s) by {
                crate::pmem::pmemutil_v::lemma_can_result_from_partial_write_effect(s, power_pm@.durable_state, self.addr as int, seq![self.val0]);
            }

            power_pm.write(self.addr, vec![self.val0].as_slice(), Tracked(perm));
            power_pm.write(self.addr, vec![self.val1].as_slice(), Tracked(perm));
            power_pm.flush();

            power_pm.write(self.addr, vec![self.val1].as_slice(), Tracked(perm));
            power_pm.write(self.addr, vec![self.val0].as_slice(), Tracked(perm));
            power_pm.flush();
        }
    }
}

struct DurableResource {
    r: Frac<Seq<u8>>,
}

struct DurablePredicate<PM, S>
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
{
    id: int,
    sound: S,
    _pm: core::marker::PhantomData<PM>,
}

impl<PM, S> InvariantPredicate<DurablePredicate<PM, S>, DurableResource> for DurablePredicate<PM, S>
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
{
    closed spec fn inv(k: DurablePredicate<PM, S>, inner: DurableResource) -> bool {
        &&& inner.r.valid(k.id, 1)
        &&& k.sound.valid(inner.r@)
    }
}

struct SoundnessPermission<PM, S>
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
{
    inv: AtomicInvariant::<DurablePredicate<PM, S>, DurableResource, DurablePredicate<PM, S>>,
}

impl<PM, S> CheckPermission<Seq<u8>> for SoundnessPermission<PM, S>
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
{
    closed spec fn check_permission(&self, state: Seq<u8>) -> bool {
        self.inv.constant().sound.valid(state)
    }

    closed spec fn valid(&self, id: int) -> bool {
        self.inv.constant().id == id
    }

    proof fn apply(tracked &self, tracked credit: OpenInvariantCredit, tracked r: &mut Frac<Seq<u8>>, new_state: Seq<u8>) {
        open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
            r.update_with(&mut inner.r, new_state);
        });
    }
}

// The soundness_setup() function models what happens the first time
// persistent memory is initialized by the application: the soundness
// predicate is only established once the application finishes setup,
// and keeps being true at all points after that.
exec fn soundness_setup<PM, S>(mut pm: PM, s: S)
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
    requires
        pm.inv(),
{
    // Initialize the contents of the persistent memory.
    s.setup(&mut pm);

    // Set up the atomic invariant to keep track of the durable state.
    let (mut pm_atomic, Tracked(r)) = PersistentMemoryRegionAtomic::new(pm);

    let ghost pred = DurablePredicate{
        id: r.id(),
        sound: s,
        _pm: core::marker::PhantomData,
    };

    let tracked inv_res = DurableResource{
        r: r
    };

    let tracked inv = AtomicInvariant::<_, _, DurablePredicate<PM, S>>::new(pred, inv_res, 0);

    // Establish that the read state matches the durable state.
    pm_atomic.flush();

    // Construct a permission that captures the soundness predicate.
    let tracked perm = SoundnessPermission{
        inv: inv
    };

    // Allow the application to run until the next crash.
    s.recover::<SoundnessPermission::<PM, S>>(pm_atomic, Tracked(&perm))

    // Note that the atomic invariant continues to exist, and therefore
    // enforces that the durable state will still satisfy the soundness
    // predicate, at all points during the application's execution in
    // s.recover().
}

// The soundness_recover() function models what happens on recovery from
// crash once the system has already been successfully initialized by
// soundness_setup(), with zero or more additional crashes and recoveries
// after that.
exec fn soundness_recover<PM, S>(pm: PM, s: S)
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
    requires
        pm.inv(),
{
    // Construct an atomic wrapper around pm, to get a resource for durable_state.
    let (mut pm_atomic, Tracked(r)) = PersistentMemoryRegionAtomic::new(pm);

    // Restore the atomic invariant, which we assume was true before the
    // system crashed (i.e., it must have been that the previous execution
    // started with soundness_setup() and got all the way to running
    // s.recover(), or the previous execution started with soundness_recover().
    let ghost pred = DurablePredicate{
        id: r.id(),
        sound: s,
        _pm: core::marker::PhantomData,
    };

    let tracked inv = invariant_recovery_soundness_axiom(pred);

    // Open the invariant to observe that the current state satisfies valid(),
    // because the resource in the invariant agrees with `pm_atomic`.
    open_atomic_invariant!(&inv => inner => {
        proof {
            inner.r.agree(pm_atomic.res.borrow());
        }
    });

    // Establish that the read state matches the durable state, since this
    // is technically not required by the precondition of soundness_recover().
    pm_atomic.flush();

    // Construct a permission that captures the soundness predicate.
    let tracked perm = SoundnessPermission{
        inv: inv
    };

    // Allow the application to run until the next crash.
    s.recover::<SoundnessPermission::<PM, S>>(pm_atomic, Tracked(&perm))

    // Note that the atomic invariant continues to exist, and therefore
    // enforces that the durable state will still satisfy the soundness
    // predicate, at all points during the application's execution in
    // s.recover().
}

// The invariant_recovery_soundness_axiom() states a key assumption for
// the soundness argument: that an AtomicInvariant on the logically atomic
// contents of the disk still holds after recovery.  The assumption is
// that this axiom will be invoked only in situations where we know the
// AtomicInvariant held before the crash.  This models the use of atomic
// invariants that persist across crashes in Perennial.
#[verifier::external_body]
proof fn invariant_recovery_soundness_axiom<PM, S>(pred: DurablePredicate<PM, S>) -> (tracked result: AtomicInvariant::<DurablePredicate<PM, S>, DurableResource, DurablePredicate<PM, S>>)
    where
        PM: PersistentMemoryRegion,
        S: SoundnessParam<PM>,
    ensures
        result.constant() == pred,
{
    unimplemented!()
}

}
