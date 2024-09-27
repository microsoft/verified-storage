#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use crate::kv::durable::commonlayout_v::*;
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

pub open spec fn apply_physical_log_entries(mem: Seq<u8>, physical_log_entries: Seq<AbstractPhysicalOpLogEntry>) -> Option<Seq<u8>>
    decreases physical_log_entries.len()
{
    if physical_log_entries.len() == 0 {
        Some(mem)
    } else {
        let prefix = physical_log_entries.drop_last();
        let last_op = physical_log_entries.last();
        if let Some(new_mem) = apply_physical_log_entries(mem, prefix) {
            apply_physical_log_entry(new_mem, last_op)
        } else {
            None
        }
    }
}

pub open spec fn log_entry_does_not_modify_addresses(
    entry: AbstractPhysicalOpLogEntry,
    start: nat,
    len: nat,
) -> bool
{
    ||| entry.absolute_addr + entry.len <= start
    ||| entry.absolute_addr >= start + len
}


pub open spec fn log_entries_do_not_modify_item_table(
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    overall_metadata: OverallMetadata
) -> bool
{
    forall |i: nat| i < op_log.len() ==>
        log_entry_does_not_modify_addresses(#[trigger] op_log[i as int], overall_metadata.item_table_addr as nat,
                                            overall_metadata.item_table_size as nat)
}

pub open spec fn log_entry_does_not_modify_free_main_table_entry(
    entry: AbstractPhysicalOpLogEntry,
    free_index: u64,
    overall_metadata: OverallMetadata
) -> bool
{
    let start = overall_metadata.main_table_addr as nat +
                index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
    log_entry_does_not_modify_addresses(entry, start, overall_metadata.main_table_entry_size as nat)
}

pub open spec fn log_entries_do_not_modify_free_main_table_entry(
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    free_index: u64,
    overall_metadata: OverallMetadata
) -> bool
{
    forall |i: nat| i < op_log.len() ==>
        log_entry_does_not_modify_free_main_table_entry(#[trigger] op_log[i as int], free_index, overall_metadata)
}

pub open spec fn log_entry_does_not_modify_free_main_table_entries(
    entry: AbstractPhysicalOpLogEntry,
    free_indices: Set<u64>,
    overall_metadata: OverallMetadata
) -> bool
{
    forall|free_index: u64| #[trigger] free_indices.contains(free_index) ==>
        log_entry_does_not_modify_free_main_table_entry(entry, free_index, overall_metadata)
}

pub open spec fn log_entries_do_not_modify_free_main_table_entries(
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    free_indices: Set<u64>,
    overall_metadata: OverallMetadata
) -> bool
{
    forall|free_index: u64| #[trigger] free_indices.contains(free_index) ==>
        log_entries_do_not_modify_free_main_table_entry(op_log, free_index, overall_metadata)
}

pub proof fn prove_unwrap<T>(x: Option<T>) -> (result: T)
    requires
        x is Some
    ensures
        result == x.unwrap()
{
    x.unwrap()
}

pub proof fn lemma_appending_log_entry_preserves_log_entries_do_not_modify_free_main_table_entries(
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    new_entry: AbstractPhysicalOpLogEntry,
    free_indices: Set<u64>,
    overall_metadata: OverallMetadata
)
    requires
        log_entries_do_not_modify_free_main_table_entries(op_log, free_indices, overall_metadata),
        log_entry_does_not_modify_free_main_table_entries(new_entry, free_indices, overall_metadata),
    ensures
        log_entries_do_not_modify_free_main_table_entries(op_log.push(new_entry), free_indices, overall_metadata)
{
}

pub proof fn lemma_log_entry_does_not_modify_free_main_table_entries(
    entry: AbstractPhysicalOpLogEntry,
    index: u64,
    free_indices: Set<u64>,
    overall_metadata: OverallMetadata
)
    requires
        !free_indices.contains(index),
        index < overall_metadata.num_keys,
        entry.absolute_addr >=
            overall_metadata.main_table_addr +
            index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat),
        entry.absolute_addr + entry.len <=
            overall_metadata.main_table_addr +
            index_to_offset(index as nat, overall_metadata.main_table_entry_size as nat) +
            overall_metadata.main_table_entry_size,
    ensures
        log_entry_does_not_modify_free_main_table_entries(entry, free_indices, overall_metadata)
{
    assert forall|free_index: u64| #[trigger] free_indices.contains(free_index) implies
        log_entry_does_not_modify_free_main_table_entry(entry, free_index, overall_metadata) by {
        assert(index != free_index);
        lemma_entries_dont_overlap_unless_same_index(index as nat, free_index as nat,
                                                     overall_metadata.main_table_entry_size as nat);
    }
}

pub open spec fn update_bytes(s: Seq<u8>, addr: int, bytes: Seq<u8>) -> Seq<u8>
{
    Seq::new(s.len(), |i: int| if addr <= i < addr + bytes.len() { bytes[i - addr] } else { s[i] })
}

pub proof fn lemma_update_to_free_main_table_entry_commutes_with_log_entry_replay(
    mem: Seq<u8>,
    log_entry: AbstractPhysicalOpLogEntry,
    free_indices: Set<u64>,
    free_index: u64,
    main_table_entry: Seq<u8>,
    overall_metadata: OverallMetadata,
)
    requires
        main_table_entry.len() == overall_metadata.main_table_entry_size,
        log_entry_does_not_modify_free_main_table_entries(log_entry, free_indices, overall_metadata),
        free_indices.contains(free_index),
        apply_physical_log_entry(mem, log_entry) is Some,
    ensures
        ({
            let offset = index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
            let addr = overall_metadata.main_table_addr + offset;
            apply_physical_log_entry(update_bytes(mem, addr, main_table_entry), log_entry) ==
                Some(update_bytes(apply_physical_log_entry(mem, log_entry).unwrap(), addr, main_table_entry))
        })
{
    let offset = index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
    let addr = overall_metadata.main_table_addr + offset;
    assert(apply_physical_log_entry(update_bytes(mem, addr, main_table_entry), log_entry) =~=
           Some(update_bytes(apply_physical_log_entry(mem, log_entry).unwrap(), addr, main_table_entry)));
}

pub proof fn lemma_update_to_free_main_table_entry_commutes_with_log_replay(
    mem: Seq<u8>,
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    free_indices: Set<u64>,
    free_index: u64,
    main_table_entry: Seq<u8>,
    overall_metadata: OverallMetadata,
)
    requires
        main_table_entry.len() == overall_metadata.main_table_entry_size,
        log_entries_do_not_modify_free_main_table_entries(op_log, free_indices, overall_metadata),
        free_indices.contains(free_index),
        apply_physical_log_entries(mem, op_log) is Some,
    ensures
        ({
            let offset = index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
            let addr = overall_metadata.main_table_addr + offset;
            apply_physical_log_entries(update_bytes(mem, addr, main_table_entry), op_log) ==
                Some(update_bytes(apply_physical_log_entries(mem, op_log).unwrap(), addr, main_table_entry))
        })
    decreases
        op_log.len()
{
    if op_log.len() == 0 {
        return;
    }
    else {
        lemma_update_to_free_main_table_entry_commutes_with_log_replay(
            mem, op_log.drop_last(), free_indices, free_index, main_table_entry, overall_metadata
        );
        let penultimate_mem = apply_physical_log_entries(mem, op_log.drop_last()).unwrap();
        lemma_update_to_free_main_table_entry_commutes_with_log_entry_replay(
            penultimate_mem, op_log.last(), free_indices, free_index, main_table_entry, overall_metadata
        );
    }
}                

}
