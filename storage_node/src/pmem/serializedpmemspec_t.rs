use crate::pmem::pmemspec_t::*;
use crate::pmem::serialization_t::*;
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus! {

    // TODO: it's not safe for S to be a reference or to contain references.
    // How can we restrict that? Corundum did something similar....
    pub trait SerializedPmRegion<S> : Sized
    where
        S: Sized + Serializable
    {}

    pub struct WriteRestrictedSerializedPmRegion<Perm, PMRegion, S>
    where
        Perm: CheckPermission<Seq<u8>>,
        PMRegion: SerializedPmRegion<S>,
        S: Sized + Serializable
    {
        pm_region: PMRegion,
        ghost perm: Option<Perm>,
        _phantom: Ghost<Option<S>> // TODO: use PhantomData
    }
}
