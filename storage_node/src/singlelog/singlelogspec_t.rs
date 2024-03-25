use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::serializedpmemspec_t::*;
use crate::singlelog::layout_v::*;
use crate::singlelog::singlelogimpl_v::*;

verus! {

    // This trait will be an abstract representation of a storage
    // component that might contain multiple PM regions that we
    // can use to prove crash consistency.
    //
    // `CheckedPermission` objects should be generic over an implementation of
    // `MemState`. The caller is responsible for proving:
    // 1. That every `MemState` corresponding to a possible crash state
    //    maps to a legal abstract state
    // 2. That the write call will update the `MemState` in a specific way
    //
    // This trait/objects that implement it need to have the
    // following properties:
    // 1. We can view any concrete component as a `MemState`
    // 2. We can convert any `MemState` to the higher-level abstract view of the
    //    component; a concrete representation and the MemState it is viewed as
    //    must both correspond to the same abstract view
    // 3. Each operation that updates the concrete component has a corresponding
    //    operation implemented for the MemState
    pub trait MemState : Sized{
        spec fn update(self, f: spec_fn(Self) -> Self) -> Self;
    }

    pub struct LogMemState {
        cdb_mem: Seq<u8>,
        sb_mem: Seq<u8>,
        header_mem: Seq<u8>,
        data_mem: Seq<u8>,
    }

    // A `TrustedPermission` is the type of a tracked object
    // indicating permission to update memory. It restricts updates so
    // that if a crash happens, the resulting memory `mem` satisfies
    // `is_state_allowable(mem)`.
    //
    // The struct is defined in this file, and it has a non-public
    // field, so the only code that can create one is in this file.
    // So untrusted code in other files can't create one, and we can
    // rely on it to restrict access to persistent memory.
    #[allow(dead_code)]
    pub struct TrustedPermission<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>
    where
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    {
        ghost is_state_allowable: spec_fn(LogMemState) -> bool,
        _phantom: Ghost<Option<(CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm)>>
    }

    impl<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm> CheckPermission<LogMemState> for TrustedPermission<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>
    where
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
     {
        closed spec fn check_permission(&self, state: LogMemState) -> bool {
            (self.is_state_allowable)(state)
        }
    }

    impl<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm> TrustedPermission<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>
    where
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    {

        // This is one of two constructors for `TrustedPermission`.
        // It conveys permission to do any update as long as a
        // subsequent crash and recovery can only lead to given
        // abstract state `state`.
        proof fn new_one_possibility(log_id: u128, state: AbstractLogState) -> (tracked perm: Self)
            ensures
                forall |s| #[trigger] perm.check_permission(s) <==>
                    UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state)
        {
            Self {
                is_state_allowable: |s| UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state),
                _phantom: Ghost(None),
            }
        }

        // This is the second of two constructors for
        // `TrustedPermission`.  It conveys permission to do any
        // update as long as a subsequent crash and recovery can only
        // lead to one of two given abstract states `state1` and
        // `state2`.
        proof fn new_two_possibilities(
            log_id: u128,
            state1: AbstractLogState,
            state2: AbstractLogState
        ) -> (tracked perm: Self)
            ensures
            forall |s| #[trigger] perm.check_permission(s) <==> {
                    ||| UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state1)
                    ||| UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state2)
                }
        {
            Self {
                is_state_allowable: |s| {
                    ||| UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state1)
                    ||| UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(s) == Some(state2)
                },
                _phantom: Ghost(None)
            }
        }
    }

    pub open spec fn can_only_crash_as_state<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>(
        cdb_region_view: SerializedPmRegionView<u64>,
        sb_region_view: SerializedPmRegionView<S>,
        header_region_view: SerializedPmRegionView<H>,
        data_region_view: SerializedPmRegionView<D>,
        state: AbstractLogState,
    ) -> bool
        where
            CDBRegion: SerializedPmRegion<u64>,
            SRegion: SerializedPmRegion<S>,
            HRegion: SerializedPmRegion<H>,
            DRegion: SerializedPmRegion<D>,
            S: Sized + Serializable + SuperBlock,
            H: Sized + Serializable + Headers,
            D: Sized + Serializable + LogContents,
            Perm: CheckPermission<Seq<u8>>,
    {
        forall |cdb_s, sb_s, h_s, d_s| {
            &&& cdb_region_view.can_crash_as(cdb_s)
            &&& sb_region_view.can_crash_as(sb_s)
            &&& header_region_view.can_crash_as(h_s)
            &&& data_region_view.can_crash_as(d_s)
        } ==> {
            UntrustedLogImpl::<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>::recover(cdb_s, sb_s, h_s, d_s)
                == Some(state)
        }
    }

    // An `AbstractLogState` is an abstraction of a single log.
    // Its fields are:
    //
    // `head` -- the logical position of the first accessible byte
    // in the log
    //
    // `log` -- the accessible bytes in the log, logically starting
    // at position `head`
    //
    // `pending` -- the bytes tentatively appended past the end of the
    // log, which will not become part of the log unless committed
    // and which will be discarded on a crash
    //
    // `capacity` -- the maximum length of the `log` field
    #[verifier::ext_equal]
    pub struct AbstractLogState {
        pub head: int,
        pub log: Seq<u8>,
        // pub pending: Seq<u8>,
        pub capacity: int,
    }

    impl AbstractLogState {

        // This is the specification for the initial state of an
        // abstract log.
        pub open spec fn initialize(capacity: int) -> Self {
            Self {
                head: 0int,
                log: Seq::<u8>::empty(),
                // pending: Seq::<u8>::empty(),
                capacity: capacity
            }
        }

        // // This is the specification for what it means to tentatively
        // // append to a log. It appends the given bytes to the
        // // `pending` field.
        // pub open spec fn tentatively_append(self, bytes: Seq<u8>) -> Self {
        //     Self { pending: self.pending + bytes, ..self }
        // }

        pub open spec fn append(self, bytes: Seq<u8>) -> Self {
            Self { log: self.log + bytes, ..self }
        }

        // // This is the specification for what it means to commit a
        // // log.  It adds all pending bytes to the log and clears the
        // // pending bytes.
        // pub open spec fn commit(self) -> Self {
        //     Self { log: self.log + self.pending, pending: Seq::<u8>::empty(), ..self }
        // }

        // This is the specification for what it means to advance the
        // head to a given new value `new_value`.
        pub open spec fn advance_head(self, new_head: int) -> Self
        {
            let new_log = self.log.subrange(new_head - self.head, self.log.len() as int);
            Self { head: new_head, log: new_log, ..self }
        }

        // This is the specification for what it means to read `len`
        // bytes from a certain virtual position `pos` in the abstract
        // log.
        pub open spec fn read(self, pos: int, len: int) -> Seq<u8>
        {
            self.log.subrange(pos - self.head, pos - self.head + len)
        }

        // // This is the specification for what it means to drop pending
        // // appends. (This isn't a user-invokable operation; it's what
        // // happens on a crash.)
        // pub open spec fn drop_pending_appends(self) -> Self
        // {
        //     Self { pending: Seq::<u8>::empty(), ..self }
        // }
    }

    // // An intermediate log abstraction that provides a layer between
    // // the concrete log's PM regions and the high-level `AbstractLogState`.
    // // Each field is an abstraction of one of the log's concrete regions
    // // that can be used together to obtain an `AbstractLogState`.
    // //
    // // The idea is that if we can show that all crash states for a region
    // // match the corresponding field in an intermediate abstraction that
    // // then maps to a legal `AbstractLogState`, then we can prove crash consistency.
    // pub struct IntermediateAbstractLogState {
    //     // super block
    //     capacity: int,

    //     // cdb
    //     cdb: u64,

    //     // header
    //     header: AbstractHeader,

    //     // log contents
    //     log_contents: AbstractLogContents,
    // }

    // pub struct AbstractHeader {
    //     logical_head: int,
    //     logical_tail: int,
    // }

    // pub struct AbstractLogContents {
    //     bytes: Seq<u8>,
    //     pending: Seq<u8>,
    // }

}
