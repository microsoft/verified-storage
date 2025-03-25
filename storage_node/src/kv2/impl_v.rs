#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;
use super::spec_t::*;
use super::UntrustedKvStoreImpl;

verus! {

pub(super) enum KvStoreStatus
{
    Quiescent,
    MustAbort,
    ComponentsDontCorrespond,
}

impl<Perm, PM, K, I, L> UntrustedKvStoreImpl<Perm, PM, K, I, L>
where
    Perm: CheckPermission<Seq<u8>>,
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub exec fn get_keys(&self) -> (result: Result<Vec<K>, KvError>)
        requires
            self.valid(),
        ensures
            match result {
                Ok(keys) => {
                    &&& keys@.to_set() == self@.tentative.get_keys()
                    &&& keys@.no_duplicates()
                },
                Err(KvError::CRCMismatch) => !self@.pm_constants.impervious_to_corruption(),
                Err(_) => false,
            },
    {
        assert(self@.tentative.get_keys() =~= self.keys@.tentative.unwrap().key_info.dom());
        Ok(self.keys.get_keys(&self.journal))
    }

}

}
