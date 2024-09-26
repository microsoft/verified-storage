#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::kv::durable::itemtable_v::*;
use crate::kv::durable::itemtablelayout_v::*;
use crate::kv::durable::maintable_v::*;
use crate::kv::durable::maintablelayout_v::*;
use crate::kv::durable::oplog::logentry_v::*;
use crate::kv::durable::oplog::oplogimpl_v::*;
use crate::kv::layout_v::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::pmemspec_t::*;
use vstd::prelude::*;

verus! {

    pub struct MainTableRecoveryState<K>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        pub region: Seq<u8>,
        pub v: MainTableView<K>,
    }

    pub struct ItemTableRecoveryState<I>
        where 
            I: PmCopy,
    {
        pub region: Seq<u8>,
        pub v: DurableItemTableView<I>,
    }

    pub struct RecoveryState<K, I>
        where 
            K: PmCopy + std::fmt::Debug,
            I: PmCopy,
    {
        pub mem: Seq<u8>,
        pub main_table: MainTableRecoveryState<K>,
        pub item_table: ItemTableRecoveryState<I>,
    }

    pub struct DurableAndTentativeRecoveryState<K, I>
        where 
            K: PmCopy + std::fmt::Debug,
            I: PmCopy,
    {
        pub durable: RecoveryState<K, I>,
        pub tentative: RecoveryState<K, I>,
    }

    pub open spec fn apply_physical_log_entry(mem: Seq<u8>, log_op: AbstractPhysicalOpLogEntry) -> Option<Seq<u8>>
    {
        if {
            ||| log_op.absolute_addr + log_op.len > mem.len() 
            ||| log_op.bytes.len() != log_op.len
        } {
            // Return None if the log_op is ill-formed
            None
        } else {
            Some(mem.map(|pos: int, pre_byte: u8| 
                if log_op.absolute_addr <= pos < log_op.absolute_addr + log_op.len {
                    log_op.bytes[pos - log_op.absolute_addr]
                } else {
                    pre_byte
                }
            ))
        }
    }

    pub open spec fn apply_physical_log_entries(
        mem: Seq<u8>,
        physical_log_entries: Seq<AbstractPhysicalOpLogEntry>
    ) -> Option<Seq<u8>>
        decreases physical_log_entries.len()
    {
        if physical_log_entries.len() == 0 {
            Some(mem)
        } else {
            let prefix = physical_log_entries.subrange(0, physical_log_entries.len() - 1);
            let last_op = physical_log_entries[physical_log_entries.len() - 1];
            if let Some(new_mem) = apply_physical_log_entries(mem, prefix) {
                apply_physical_log_entry(new_mem, last_op)
            } else {
                None
            }

        }
    }

    pub open spec fn get_main_table_recovery_state_from_region<K>(region: Seq<u8>, overall_metadata: OverallMetadata)
        -> Option<MainTableRecoveryState<K>>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        match parse_main_table::<K>(region, overall_metadata.num_keys, overall_metadata.main_table_entry_size) {
            Some(v) => Some(MainTableRecoveryState::<K>{ region, v }),
            None => None,
        }
    }

    pub open spec fn get_main_table_recovery_state_from_mem<K>(mem: Seq<u8>, overall_metadata: OverallMetadata)
        -> Option<MainTableRecoveryState<K>>
        where 
            K: PmCopy + std::fmt::Debug,
    {
        if overall_metadata.main_table_addr + overall_metadata.main_table_size <= mem.len() {
            let main_table_region = extract_bytes(mem, overall_metadata.main_table_addr as nat,
                                                  overall_metadata.main_table_size as nat);
            get_main_table_recovery_state_from_region(main_table_region, overall_metadata)
        }
        else {
            None
        }
    }

    pub open spec fn get_item_table_recovery_state_from_region<K, I>(region: Seq<u8>, overall_metadata: OverallMetadata,
                                                                     valid_indices: Set<u64>)
        -> Option<ItemTableRecoveryState<I>>
        where 
            K: PmCopy + std::fmt::Debug,
            I: PmCopy,
    {
        match parse_item_table::<I, K>(region, overall_metadata.num_keys as nat, valid_indices) {
            Some(v) => Some(ItemTableRecoveryState::<I>{ region, v }),
            None => None,
        }
    }

    pub open spec fn get_item_table_recovery_state_from_mem<K, I>(mem: Seq<u8>, overall_metadata: OverallMetadata,
                                                                  valid_indices: Set<u64>)
        -> Option<ItemTableRecoveryState<I>>
        where 
            K: PmCopy + std::fmt::Debug,
            I: PmCopy,
    {
        if overall_metadata.item_table_addr + overall_metadata.item_table_size <= mem.len() {
            let item_table_region = extract_bytes(mem, overall_metadata.item_table_addr as nat,
                                                  overall_metadata.item_table_size as nat);
            get_item_table_recovery_state_from_region::<K, I>(item_table_region, overall_metadata, valid_indices)
        }
        else {
            None
        }
    }

    pub open spec fn get_recovery_state<K, I>(mem: Seq<u8>, overall_metadata: OverallMetadata)
        -> Option<RecoveryState<K, I>>
        where 
            K: PmCopy + std::fmt::Debug,
            I: PmCopy,
    {
        match get_main_table_recovery_state_from_mem::<K>(mem, overall_metadata) {
            Some(main_table) =>
                match get_item_table_recovery_state_from_mem::<K, I>(mem, overall_metadata,
                                                                     main_table.v.valid_item_indices()) {
                    Some(item_table) => Some(RecoveryState::<K, I>{ mem, main_table, item_table }),
                    None => None,
                },
            None => None,
        }
    }

    pub open spec fn get_durable_and_tentative_recovery_state<K, I>(
        mem: Seq<u8>,
        ops: Seq<AbstractPhysicalOpLogEntry>,
        overall_metadata: OverallMetadata
    )
        -> Option<DurableAndTentativeRecoveryState<K, I>>
        where 
            I: PmCopy,
            K: PmCopy + std::fmt::Debug,
    {
        match apply_physical_log_entries(mem, ops) {
            Some(mem_with_op_log_applied) =>
                match (get_recovery_state(mem, overall_metadata),
                       get_recovery_state(mem_with_op_log_applied, overall_metadata)) {
                    (Some(durable), Some(tentative)) => Some(DurableAndTentativeRecoveryState{ durable, tentative }),
                    (_, _) => None,
                },
            None => None,
        }
    }

    pub proof fn prove_unwrap<T>(x: Option<T>) -> (result: T)
        requires
            x is Some
        ensures
            result == x.unwrap()
    {
        x.unwrap()
    }
}
