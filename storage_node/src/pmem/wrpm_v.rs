use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {
/// A `WriteRestrictedPersistentMemoryRegions` is a wrapper around a
/// collection of persistent memory regions that restricts how it can
/// be written. Specifically, it only permits a write if it's
/// accompanied by a tracked permission authorizing that write. The
/// tracked permission must authorize every possible state that could
/// result from crashing while the write is ongoing.

pub trait CheckPermission<State>
{
    spec fn check_permission(&self, state: State) -> bool;
}

// // This trait helps us obtain permissions structures about individual components
// // from higher-level perm definitions. `OuterState` refers to the more general/higher-level
// // perm; `InnerState` refers to the more specific/lower-level perm. For example,
// // `TrustedKvPermission` may be an `OuterState` and `TrustedMultiLogPermission`
// // may be an `InnerState`.
// // TODO: right now this only works with inner structures that do not require
// // input to their recovery fn (e.g. the log). We need a variation on this
// // to handle additional recovery information.
// // TODO: does this need to use tracked values? do we need to ensure that
// // there is at most one converted permission at a time?
// pub trait FromPerm<P, OuterState, InnerState> : CheckPermission<InnerState> + Sized
//     where
//         P: CheckPermission<OuterState>
// {
//     spec fn from(perm: &P) -> Self;

//     spec fn states_correspond(outer_state: OuterState, inner_state: InnerState) -> bool;

//     // This lemma proves that the Perm structure obtained using `Self::from`
//     // only allows crash states that are also legal in the context of the outer
//     // permission
//     proof fn lemma_perm_conversion_preserves_crash_consistency(&self, from_perm: &P)
//         requires
//             Self::from(from_perm) == self
//         ensures
//             forall |s1: InnerState, s2: OuterState| {
//                 &&& from_perm.check_permission(s2)
//                 &&& Self::states_correspond(s2, s1)
//             } <==> self.check_permission(s1)
//     ;
// }

#[allow(dead_code)]
pub struct WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>
    where
        Perm: CheckPermission<Seq<Seq<u8>>>,
        PMRegions: PersistentMemoryRegions
{
    pm_regions: PMRegions,
    ghost perm: Option<Perm>, // Needed to work around Rust limitation that Perm must be referenced
}

impl<Perm, PMRegions> WriteRestrictedPersistentMemoryRegions<Perm, PMRegions>
    where
        Perm: CheckPermission<Seq<Seq<u8>>>,
        PMRegions: PersistentMemoryRegions
{
    pub closed spec fn view(&self) -> PersistentMemoryRegionsView
    {
        self.pm_regions@
    }

    pub closed spec fn inv(&self) -> bool
    {
        self.pm_regions.inv()
    }

    pub closed spec fn constants(&self) -> PersistentMemoryConstants
    {
        self.pm_regions.constants()
    }

    pub exec fn new(pm_regions: PMRegions) -> (wrpm_regions: Self)
        requires
            pm_regions.inv()
        ensures
            wrpm_regions.inv(),
            wrpm_regions@ == pm_regions@,
            wrpm_regions.constants() == pm_regions.constants()
    {
        Self {
            pm_regions: pm_regions,
            perm: None
        }
    }

    // This executable function returns an immutable reference to the
    // persistent memory regions. This can be used to perform any
    // operation (e.g., read) that can't mutate the memory. After all,
    // this is a write-restricted memory, not a read-restricted one.
    pub exec fn get_pm_regions_ref(&self) -> (pm_regions: &PMRegions)
        requires
            self.inv(),
        ensures
            pm_regions.inv(),
            pm_regions@ == self@,
            pm_regions.constants() == self.constants()
    {
        &self.pm_regions
    }

    // This executable function is the only way to perform a write, and
    // it requires the caller to supply permission authorizing the
    // write. The caller must prove that for every state this memory
    // can crash and recover into, the permission authorizes that
    // state.
    #[allow(unused_variables)]
    pub exec fn write(&mut self, index: usize, addr: u64, bytes: &[u8], perm: Tracked<&Perm>)
        requires
            old(self).inv(),
            index < old(self)@.len(),
            addr + bytes@.len() <= old(self)@[index as int].len(),
            addr + bytes@.len() <= u64::MAX,
            old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + bytes@.len()),
            ({
                // The key thing the caller must prove is that all crash states are authorized by `perm`
                &&& forall |s| {
                        let pm_state = old(self)@.write(index as int, addr as int, bytes@);
                        pm_state.can_crash_as(s)
                    } ==> #[trigger] perm@.check_permission(s)
            }),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            ({
                let written = old(self)@.write(index as int, addr as int, bytes@);
                &&& self@ == written
            }),
            self@.timestamp == old(self)@.timestamp

    {
        self.pm_regions.write(index, addr, bytes)
    }

    #[allow(unused_variables)]
    pub exec fn serialize_and_write<S>(&mut self, index: usize, addr: u64, to_write: &S, perm: Tracked<&Perm>)
        where
            S: Serializable + Sized
        requires
            old(self).inv(),
            index < old(self)@.len(),
            addr + S::spec_serialized_len() <= old(self)@[index as int].len(),
            old(self)@.no_outstanding_writes_in_range(index as int, addr as int, addr + S::spec_serialized_len()),
            ({
                // The key thing the caller must prove is that all crash states are authorized by `perm`
                &&& forall |s| {
                        let pm_state = old(self)@.write(index as int, addr as int, to_write.spec_serialize());
                        pm_state.can_crash_as(s)
                    } ==> #[trigger] perm@.check_permission(s)
            }),
        ensures
            self.inv(),
            self.constants() == old(self).constants(),
            self@.timestamp == old(self)@.timestamp,
            ({
                let written = old(self)@.write(index as int, addr as int, to_write.spec_serialize());
                self@ == written
            })
    {
        self.pm_regions.serialize_and_write(index, addr, to_write);
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
            self.inv(),
            ({
                let flushed = old(self)@.flush();
                &&& self@ == flushed
            }),
            self.constants() == old(self).constants(),
            self@.timestamp.value() == old(self)@.timestamp.value() + 1,
            self@.timestamp.device_id() == old(self)@.timestamp.device_id()
    {
        self.pm_regions.flush()
    }

    pub fn update_timestamps(&mut self, new_timestamp: Ghost<PmTimestamp>)
        requires
            old(self).inv(),
            new_timestamp@.gt(old(self)@.timestamp),
            new_timestamp@.device_id() == old(self)@.timestamp.device_id()
        ensures
            self.inv(),
            self@.timestamp == new_timestamp@,
            self@.equal_except_for_timestamps(old(self)@),
            forall |s| old(self)@.can_crash_as(s) <==> self@.can_crash_as(s)
    {
        self.pm_regions.update_timestamps(new_timestamp);
    }
}
}
