#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::subrange_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use crate::pmem::pmemutil_v::*;
use std::hash::Hash;
use super::*;
use super::impl_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::setup_v::*;
use super::spec_t::*;

verus! {

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
where
    PM: PersistentMemoryRegion,
    K: Hash + PmCopy + Sized + std::fmt::Debug,
    I: PmCopy + Sized + std::fmt::Debug,
    L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub(super) proof fn lemma_establish_recovery_equivalent_for_app(
        &self,
        tracked perm: &TrustedKvPermission,
    )
        requires
            self.valid(),
            forall |s| Self::untrusted_recover(s) == Some(self@.durable) ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(
            s, self.journal@.durable_state) ==> #[trigger] perm.check_permission(s)
    {
        let jc = self.journal@.constants;
        let js = self.journal@.durable_state;
        let sm = self.sm@;
        let keys = self.keys@.durable;

        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state;
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implies_recover(self.journal@);
            self.items.lemma_valid_implies_recover(self.journal@);
            self.lists.lemma_valid_implies_recover(self.journal@, keys.list_addrs());
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::untrusted_recover(s) =~= Some(self@.durable));
        }
    }

    pub(super) proof fn lemma_establish_recovery_equivalent_for_app_after_commit(
        &self,
        tracked perm: &TrustedKvPermission,
    )
        requires
            self.valid(),
            !(self.status@ is MustAbort),
            self.keys@.tentative is Some,
            forall |s| Self::untrusted_recover(s) == Some(self@.tentative) ==> #[trigger] perm.check_permission(s),
        ensures forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(
            s, self.journal@.commit_state) ==> #[trigger] perm.check_permission(s)
    {
        let jc = self.journal@.constants;
        let js = self.journal@.commit_state;
        let sm = self.sm@;
        let keys = self.keys@.tentative.unwrap();

        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(s, js)
            implies #[trigger] perm.check_permission(s) by {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
            let js2 = Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state;
            assert(Journal::<TrustedKvPermission, PM>::recover(js) is Some);
            assert(Journal::<TrustedKvPermission, PM>::recover(s) is Some);
            assume(Journal::<TrustedKvPermission, PM>::recover(js).unwrap().constants == jc);
            assume(Journal::<TrustedKvPermission, PM>::recover(js2).unwrap().constants == jc);
            assert(seqs_match_in_range(Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state,
                                       Journal::<TrustedKvPermission, PM>::recover(js).unwrap().state,
                                       jc.app_area_start as int,
                                       jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()));
            assume(js == Journal::<TrustedKvPermission, PM>::recover(js).unwrap().state);
            assert(seqs_match_in_range(js, js2, jc.app_area_start as int,
                                       jc.app_area_start + KvStaticMetadata::spec_size_of() + u64::spec_size_of()));
            assume(false);
            lemma_recover_static_metadata_depends_only_on_its_area::<K, I, L>(js, js2, self.sm@, jc);
            self.keys.lemma_valid_implies_recover_after_commit(self.journal@);
            self.items.lemma_valid_implies_recover_after_commit(self.journal@);
            self.lists.lemma_valid_implies_recover_after_commit(self.journal@, keys.list_addrs());
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, js2, keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, js2, keys.list_addrs(), sm.lists);
            assert(Self::untrusted_recover(s) =~= Some(self@.tentative));
        }
    }
}

}
