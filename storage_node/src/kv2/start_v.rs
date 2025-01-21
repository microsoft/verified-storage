#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use super::impl_t::*;
use super::items::*;
use super::keys::*;
use super::lists::*;
use super::recover_v::*;
use super::spec_t::*;
use super::*;
use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;

verus! {

impl<PM, K, I, L> UntrustedKvStoreImpl<PM, K, I, L>
    where
        PM: PersistentMemoryRegion,
        K: Hash + PmCopy + std::fmt::Debug,
        I: PmCopy + std::fmt::Debug,
        L: PmCopy + LogicalRange + std::fmt::Debug + Copy,
{
    pub fn untrusted_start(
        wrpm: WriteRestrictedPersistentMemoryRegion<TrustedKvPermission, PM>,
        kvstore_id: u128,
        Ghost(state): Ghost<AtomicKvStore<K, I, L>>,
        Tracked(perm): Tracked<&TrustedKvPermission>,
    ) -> (result: Result<Self, KvError>)
        requires
            wrpm.inv(),
            Self::untrusted_recover(wrpm@.durable_state) == Some(state),
            vstd::std_specs::hash::obeys_key_model::<K>(),
            forall |s| #[trigger] perm.check_permission(s) <==> Self::untrusted_recover(s) == Some(state),
        ensures
            match result {
                Ok(kv) => {
                    &&& kv.valid()
                    &&& kv@.valid()
                    &&& kv@.id == state.id == kvstore_id
                    &&& kv@.logical_range_gaps_policy == state.logical_range_gaps_policy
                    &&& kv@.pm_constants == wrpm.constants()
                    &&& kv@.durable == state
                    &&& kv@.tentative == state
                }
                Err(KvError::CRCMismatch) => !wrpm.constants().impervious_to_corruption(),
                Err(KvError::WrongKvStoreId{ requested_id, actual_id }) => {
                   &&& requested_id == kvstore_id
                   &&& actual_id == state.id
                },
                Err(KvError::KeySizeTooSmall) => K::spec_size_of() == 0,
                Err(_) => false,
            }
    {
        reveal(recover_static_metadata);
        let ghost old_state = wrpm@.durable_state;
        let ghost journal_recovered = Journal::<TrustedKvPermission, PM>::recover(old_state).unwrap();
        let ghost jc = journal_recovered.constants;
        let ghost js = journal_recovered.state;
        let ghost sm = recover_static_metadata::<K, I, L>(js, jc).unwrap();
        let ghost recovered_keys = KeyTable::<PM, K>::recover(js, sm.keys).unwrap();
        let ghost recovered_items = ItemTable::<PM, I>::recover(js, recovered_keys.item_addrs(), sm.items).unwrap();
        let ghost recovered_lists = ListTable::<PM, L>::recover(js, recovered_keys.list_addrs(), sm.lists).unwrap();

        proof {
            broadcast use broadcast_seqs_match_in_range_can_narrow_range;
        }

        assert forall|s: Seq<u8>| Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(s, old_state)
                   implies #[trigger] perm.check_permission(s) by {
            let js2 = Journal::<TrustedKvPermission, PM>::recover(s).unwrap().state;
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, js2, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, js2, recovered_keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, js2, recovered_keys.list_addrs(), sm.lists);
        }

        let journal = match Journal::<TrustedKvPermission, PM>::start(wrpm, Tracked(perm)) {
            Ok(j) => j,
            Err(JournalError::CRCError) => { return Err(KvError::CRCMismatch); },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let jc: &JournalConstants = journal.constants();

        if jc.app_program_guid != KVSTORE_PROGRAM_GUID {
            assert(false);
            return Err(KvError::InternalError);
        }
        if jc.app_version_number != KVSTORE_PROGRAM_VERSION_NUMBER {
            assert(false);
            return Err(KvError::InternalError);
        }

        assert(journal.recover_idempotent());
        assert(Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(journal@.read_state, old_state));
        assert(seqs_match_in_range(journal@.read_state, js, jc.app_area_start as int, jc.app_area_end as int));

        let sm = match exec_recover_object::<PM, KvStaticMetadata>(
            journal.get_pm_region_ref(), jc.app_area_start, jc.app_area_start + size_of::<KvStaticMetadata>() as u64
        ) {
            Some(sm) => sm,
            None => { return Err(KvError::CRCMismatch); },
        };
        if sm.id != kvstore_id {
            return Err(KvError::WrongKvStoreId{ requested_id: kvstore_id, actual_id: sm.id });
        }

        let logical_range_gaps_policy = match decode_policies(sm.encoded_policies) {
            Some(p) => p,
            None => { assert(false); return Err(KvError::InternalError); }
        };

        proof {
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, journal@.read_state, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, journal@.read_state,
                                                                      recovered_keys.item_addrs(), sm.items);
            ListTable::<PM, L>::lemma_recover_depends_only_on_my_area(js, journal@.read_state,
                                                                      recovered_keys.list_addrs(), sm.lists);
        }

        let (keys, item_addrs, list_addrs) = match KeyTable::<PM, K>::start(&journal, &sm.keys) {
            Ok((k, i, l)) => (k, i, l),
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let items = match ItemTable::<PM, I>::start::<K>(&journal, &item_addrs, &sm.items) {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let lists = match ListTable::<PM, L>::start::<K>(&journal, logical_range_gaps_policy, &list_addrs, &sm.lists) {
            Ok(i) => i,
            Err(KvError::CRCMismatch) => { return Err(KvError::CRCMismatch); },
            _ => { assert(false); return Err(KvError::InternalError); },
        };
        assert(lists@.durable.m.dom() == list_addrs@.to_set().insert(0));

        let kv = UntrustedKvStoreImpl::<PM, K, I, L>{
            status: Ghost(KvStoreStatus::Quiescent),
            id: sm.id,
            sm: Ghost(sm),
            journal,
            keys,
            items,
            lists,
        };
        Ok(kv)
    }
}

}
