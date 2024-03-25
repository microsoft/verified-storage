use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use crate::pmem::serializedpmemspec_t::*;
use crate::singlelog::layout_v::*;
use crate::singlelog::singlelogimpl_v::*;
use crate::singlelog::singlelogspec_t::*;

verus! {

    #[derive(Debug)]
    pub enum LogErr {
        CantSetupWithFewerThanOneRegion { },
        CantSetupWithMoreThanU32MaxRegions { },
        InsufficientSpaceForSetup { required_space: u64 },
        StartFailedDueToMultilogIDMismatch { log_id_expected: u128, log_id_read: u128 },
        StartFailedDueToRegionSizeMismatch { region_size_expected: u64, region_size_read: u64 },
        StartFailedDueToProgramVersionNumberUnsupported { version_number: u64, max_supported: u64 },
        StartFailedDueToInvalidMemoryContents { },
        CRCMismatch,
        InvalidLogIndex { },
        InsufficientSpaceForAppend { available_space: u64 },
        CantReadBeforeHead { head: u128 },
        CantReadPastTail { tail: u128 },
        CantAdvanceHeadPositionBeforeHead { head: u128 },
        CantAdvanceHeadPositionBeyondTail { tail: u128 },
        NotImplemented
    }


    pub struct LogImpl<
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    > {
        untrusted_log_impl: UntrustedLogImpl<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>,
        log_id: Ghost<u128>,
    }

    impl<
        CDBRegion: SerializedPmRegion<u64>,
        SRegion: SerializedPmRegion<S>,
        HRegion: SerializedPmRegion<H>,
        DRegion: SerializedPmRegion<D>,
        S: Sized + Serializable + SuperBlock,
        H: Sized + Serializable + Headers,
        D: Sized + Serializable + LogContents,
        Perm: CheckPermission<LogMemState>,
    > LogImpl<CDBRegion, SRegion, HRegion, DRegion, S, H, D, Perm>
    {
        pub closed spec fn view(self) -> AbstractLogState
        {
            self.untrusted_log_impl@
        }

        pub closed spec fn valid(self) -> bool {
            &&& self.untrusted_log_impl.inv()
        }
    }
}
