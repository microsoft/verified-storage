use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::timestamp_t::*;
use crate::singlelog::singlelogspec_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    pub enum SerializedPmError {
        InsufficientSpaceForRead { available_space: u64 }
    }

    pub struct SerializedEntry<S>
    where
        S: Sized + Serializable
    {
        pub state_at_last_flush: S,
        pub outstanding_write: Option<S>,
    }

    impl<S> SerializedEntry<S>
    where
        S: Sized + Serializable
    {
        pub open spec fn write(self, new_val: S) -> Self
        {
            Self {
                state_at_last_flush: self.state_at_last_flush,
                outstanding_write: Some(new_val)
            }
        }

        pub open spec fn flush_entry(self) -> S
        {
            match self.outstanding_write {
                Some(val) => val,
                None => self.state_at_last_flush
            }
        }

        pub open spec fn flush(self) -> Self
        {
            Self {
                state_at_last_flush: self.flush_entry(),
                outstanding_write: None,
            }
        }

        pub open spec fn serialize_to_pm_bytes(self) -> Seq<PersistentMemoryByte>
        {
            let flushed_bytes = self.state_at_last_flush.spec_serialize();
            let outstanding_bytes = match self.outstanding_write {
                Some(val) => {
                    Some(val.spec_serialize())
                }
                None => None
            };
            Seq::new(S::spec_serialized_len() as nat, |i| {
                PersistentMemoryByte {
                    state_at_last_flush: flushed_bytes[i],
                    outstanding_write: match outstanding_bytes {
                        Some(bytes) => Some(bytes[i]),
                        None => None,
                    },
                }
            })
        }
    }

    // TODO: it's not safe for S to be a reference or to contain references.
    // How can we restrict that? Corundum did something similar....
    pub trait SerializedPmRegion<S> : Sized
    where
        S: Sized + Serializable
    {
        spec fn inv(&self) -> bool;

        spec fn view(&self) -> SerializedPmRegionView<S>;

        spec fn get_timestamp(&self) -> PmTimestamp;

        fn write(&mut self, index: u64, new_vals: &[S], new_timestamp: Ghost<PmTimestamp>)
            requires
                old(self)@.no_outstanding_writes(),
                0 <= index <= old(self)@.len()
            ensures
                ({
                    let written = old(self)@.write(index as int, new_vals@, new_timestamp@);
                    self@ == written
                })
        ;

        fn read(&self, index: u64, num_vals: u64) -> (result: Result<&[S], SerializedPmError>)
            requires
                self@.no_outstanding_writes(),
                0 <= index <= self@.len(),
            ensures
                match result {
                    Ok(output) => {
                        output@ == self@.committed().subrange(index as int, index + num_vals)
                    }
                    Err(_) => true // TODO
                }
        ;
    }

    pub struct SerializedPmRegionView<S>
    where
        S: Sized + Serializable
    {
        contents: Seq<SerializedEntry<S>>,
        device_id: u128,
        timestamp: PmTimestamp,
    }

    impl<S> SerializedPmRegionView<S>
    where
        S: Sized + Serializable
    {
        pub closed spec fn no_outstanding_writes(self) -> bool
        {
            forall |i| #![auto] 0 <= i < self.contents.len() ==>
                self.contents[i].outstanding_write.is_None()
        }

        pub closed spec fn committed(self) -> Seq<S>
        {
            self.contents.map(|_i, s: SerializedEntry<S>| s.state_at_last_flush)
        }

        pub closed spec fn len(self) -> nat
        {
            self.contents.len()
        }

        pub closed spec fn write(&self, index: int, new_vals: Seq<S>, new_timestamp: PmTimestamp) -> Self
        {
            Self {
                contents: Seq::new(self.contents.len(), |i| {
                    if index <= i < index + new_vals.len() {
                        self.contents[i].write(new_vals[i])
                    } else {
                        self.contents[i]
                    }
                }),
                device_id: self.device_id,
                timestamp: new_timestamp,
            }
        }

        pub closed spec fn serialize_to_pm_bytes(&self) -> Seq<PersistentMemoryByte>
        {
            let bytes_seq = Seq::new(self.contents.len(), |i| self.contents[i].serialize_to_pm_bytes());
            bytes_seq.flatten()
        }

        pub closed spec fn view_as_pm_region_view(&self) -> PersistentMemoryRegionView
        {
            let state = self.serialize_to_pm_bytes();
            PersistentMemoryRegionView {
                state,
                device_id: self.device_id,
                current_timestamp: self.timestamp,
            }
        }

        // TODO: for this to work need to first convert to a PersistentMemoryRegionView
        pub open spec fn can_crash_as(&self, state: Seq<u8>) -> bool {
            let pm_region_view = self.view_as_pm_region_view();
            pm_region_view.can_crash_as(state)
        }
    }

    pub struct WriteRestrictedSerializedPmRegion<Perm, PMRegion, S, M>
    where
        Perm: CheckPermission<M>,
        PMRegion: SerializedPmRegion<S>,
        S: Sized + Serializable,
        M: Sized + MemState
    {
        pm_region: PMRegion,
        ghost perm: Option<Perm>,
        _phantom: Ghost<Option<(S, M)>> // TODO: use PhantomData
    }

    impl<Perm, PMRegion, S, M> WriteRestrictedSerializedPmRegion<Perm, PMRegion, S, M>
    where
        Perm: CheckPermission<M>,
        PMRegion: SerializedPmRegion<S>,
        S: Sized + Serializable,
        M: Sized + MemState
    {
        pub closed spec fn view(&self) -> SerializedPmRegionView<S>
        {
            self.pm_region@
        }

        // TODO: need to think about how to represent corruption
        pub exec fn read(
            &self,
            index: u64,
            num_entries: u64
        ) -> (result: Result<&[S], SerializedPmError>)
            requires
                self@.no_outstanding_writes(), // TODO: should be no outstanding writes in range?
                0 <= index <= self@.len(),
            ensures
                match result {
                    Ok(output) => {
                        &&& output@ =~= self@.committed().subrange(index as int, index + num_entries)
                    }
                    Err(_) => true // TODO: update with actual error postconditions
                }
        {
            self.pm_region.read(index, num_entries)
        }

        pub exec fn write(
            &mut self,
            index: u64, // index in terms of S, not byte offset in the region
            new_vals: &[S],
            new_timestamp: Ghost<PmTimestamp>,
            perm: Tracked<&Perm>
        )
            requires
                old(self)@.no_outstanding_writes(), // TODO: should be no outstanding writes in range?
                0 <= index <= old(self)@.len(),
                // I think this precondition can stay the same, but how we determine
                // the permissions is going to change...?
                ({
                    forall |s| {
                        let pm_state = old(self)@.write(index as int, new_vals@, new_timestamp@);
                        pm_state.can_crash_as(s)
                    } ==> perm@.check_permission(s)
                })
            ensures
                ({
                    let written = old(self)@.write(index as int, new_vals@, new_timestamp@);
                    self@ == written
                })
        {
            self.pm_region.write(index, new_vals, new_timestamp)
        }
    }
}
