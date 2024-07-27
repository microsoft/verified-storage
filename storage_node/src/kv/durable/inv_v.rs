use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use crate::{kv::layout_v::OverallMetadata, pmem::pmemspec_t::*, DurableKvStore};
use crate::kv::durable::oplog::oplogspec_t::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::kvspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::wrpm_t::*;
use std::hash::Hash;

verus! {
    // This lemma proves that an index that is less than num_keys (i.e., within bounds of the table) 
    // represents a valid table entry that we can read and parse.
    pub proof fn lemma_valid_entry_index(index: nat, num_keys: nat, size: nat)
        requires
            index < num_keys
        ensures 
            (index + 1) * size == index * size + size <= num_keys * size
    {
        vstd::arithmetic::mul::lemma_mul_inequality(index + 1 as int, num_keys as int, size as int);
        vstd::arithmetic::mul::lemma_mul_basics(size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int,
                                                                        index as int, 1);
    }

    // This lemma proves that a subrange of a subrange is equal to just obtaining the final subrange using its 
    // absolute start index. This is obvious and requires no body, but having a dedicated lemma helps
    // Z3 establish the equality
    // TODO: do this about subranges rather than extract_bytes -- should be equivalent and more useful
    pub proof fn lemma_subrange_of_extract_bytes_equal(mem: Seq<u8>, start1: nat, start2: nat, len1: nat, len2: nat)
        requires 
            start1 <= start2 <= start2 + len2 <= start1 + len1 <= mem.len()
        ensures 
            ({
                let start_offset = start2 - start1;
                extract_bytes(extract_bytes(mem, start1, len1), start_offset as nat, len2) =~= 
                    extract_bytes(mem, start2, len2)
            })
    {}

    pub proof fn lemma_safe_recovery_writes<PM, K, I, L>(
        pm_region: PersistentMemoryRegionView,
        overall_metadata: OverallMetadata,
        op_log: AbstractOpLogState<L>,
        perm: &TrustedKvPermission<PM>,
        addr: int,
        bytes: Seq<u8>,
    )
        where 
            PM: PersistentMemoryRegion,
            K: Hash + Eq + Clone + PmCopy + Sized + std::fmt::Debug,
            I: PmCopy + Sized + std::fmt::Debug,
            L: PmCopy + std::fmt::Debug + Copy,
        requires
            // pm_region.inv(),
            op_log.physical_op_list.len() > 0,
            op_log == UntrustedOpLog::<K, L>::recover(pm_region.committed(), overall_metadata).unwrap(),
            DurableKvStore::<PM, K, I, L>::physical_recover(pm_region.committed(), overall_metadata) is Some,
            // the only thing we are allowed to do is recover to the specified state
            forall |s| #[trigger] perm.check_permission(s) <==> DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) == 
                DurableKvStore::<PM, K, I, L>::physical_recover(pm_region.committed(), overall_metadata),
            0 <= addr < addr + bytes.len() < pm_region.len(),
            ({
                let addr_modified_by_recovery = |i: int| {
                    exists |j: int| 0 <= j < op_log.physical_op_list.len() ==> {
                        #[trigger] op_log.physical_op_list[j].absolute_addr <= i < op_log.physical_op_list[j].absolute_addr + #[trigger] op_log.physical_op_list[j].len
                    }
                };
                forall |i: int| addr <= i < addr + bytes.len() ==> #[trigger] addr_modified_by_recovery(i)
            })
        ensures
            ({
                // if we can crash as s, recovering s is equivalent to recovering the original state
                forall |s| pm_region.write(addr, bytes).can_crash_as(s) ==> {
                    &&& DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) matches Some(crash_recover_state)
                    &&& crash_recover_state == DurableKvStore::<PM, K, I, L>::physical_recover(pm_region.committed(), overall_metadata).unwrap()
                    &&& perm.check_permission(s)
                }
                // let addr_modified_by_recovery = |i: int| {
                //     exists |j: int| 0 <= j < op_log.physical_op_list.len() ==> {
                //         #[trigger] op_log.physical_op_list[j].absolute_addr <= i < op_log.physical_op_list[j].absolute_addr + #[trigger] op_log.physical_op_list[j].len
                //     }
                // };
                // // forall writes that only access addrs modified by recovery, the write is crash safe because recovering from the crashed state is equivalent
                // // to recovering from the original state
                // forall |addr: int, bytes: Seq<u8>| #![trigger pm_region.write(addr, bytes)] { 
                //     &&& 0 <= addr < addr + bytes.len() < pm_region.len() 
                //     &&& forall |i: int| addr <= i < addr + bytes.len() ==> #[trigger] addr_modified_by_recovery(i)
                // } ==> {
                //     // if we can crash as s, recovering s is equivalent to recovering the original state
                //     forall |s| pm_region.write(addr, bytes).can_crash_as(s) ==> {
                //         &&& DurableKvStore::<PM, K, I, L>::physical_recover(s, overall_metadata) matches Some(crash_recover_state)
                //         &&& crash_recover_state == DurableKvStore::<PM, K, I, L>::physical_recover(pm_region.committed(), overall_metadata).unwrap()
                //         &&& perm.check_permission(s)
                //     }
                // }
            })
    {
        // TODO: once you are reasonably sure that this is what you need to prove that recovery is safe, prove it!
        assume(false);
    }

}