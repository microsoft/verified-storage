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

}
