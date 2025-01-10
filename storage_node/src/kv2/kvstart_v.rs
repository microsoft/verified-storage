#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

use crate::common::align_v::*;
use crate::common::overflow_v::*;
use crate::common::recover_v::*;
use crate::common::subrange_v::*;
use crate::common::table_v::*;
use crate::common::util_v::*;
use crate::journal::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemutil_v::*;
use crate::pmem::traits_t::*;
use deps_hack::PmCopy;
use std::hash::Hash;
use super::*;
use super::keys::*;
use super::items::*;
use super::kvimpl_t::*;
use super::kvrecover_v::*;
use super::kvspec_t::*;
use super::lists::*;

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
    ) -> (result: Result<Self, KvError<K>>)
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

        let (journal, jc) = match Journal::<TrustedKvPermission, PM>::start(wrpm, Tracked(perm)) {
            Ok((j, c)) => (j, c),
            Err(JournalError::CRCError) => { return Err(KvError::CRCMismatch); },
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        assert(journal.recover_successful());
        assert(Journal::<TrustedKvPermission, PM>::recovery_equivalent_for_app(journal@.read_state, old_state));
        assert(Journal::<TrustedKvPermission, PM>::recover(journal@.read_state).unwrap().state == journal@.read_state);
        assert(seqs_match_in_range(journal@.read_state, js, jc.app_area_start as int, jc.app_area_end as int));

        let sm = match journal.read_object::<KvStaticMetadata>(
            jc.app_area_start, jc.app_area_start + size_of::<KvStaticMetadata>() as u64
        ) {
            Some(sm) => sm,
            None => { return Err(KvError::CRCMismatch); },
        };

        proof {
            KeyTable::<PM, K>::lemma_recover_depends_only_on_my_area(js, journal@.read_state, sm.keys);
            ItemTable::<PM, I>::lemma_recover_depends_only_on_my_area(js, journal@.read_state,
                                                                      recovered_keys.item_addrs(), sm.items);
        }

        let (keys, item_addrs, list_addrs) = match KeyTable::<PM, K>::start(&journal, &sm.keys) {
            Ok((k, i, l)) => (k, i, l),
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        let items = match ItemTable::<PM, I>::start::<K>(&journal, &item_addrs, &sm.items) {
            Ok(i) => i,
            _ => { assert(false); return Err(KvError::InternalError); },
        };

        assume(false);
        Err(KvError::NotImplemented)
    }
}
    
}
