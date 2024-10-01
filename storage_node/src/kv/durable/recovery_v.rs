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
use vstd::assert_seqs_equal;
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

    lemma_update_to_free_main_table_entry_commutes_with_log_replay(
        mem, op_log.drop_last(), free_indices, free_index, main_table_entry, overall_metadata
    );
    let penultimate_mem = apply_physical_log_entries(mem, op_log.drop_last()).unwrap();
    
    let offset = index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
    let addr = overall_metadata.main_table_addr + offset;
    let log_entry = op_log.last();
    assert(apply_physical_log_entry(update_bytes(penultimate_mem, addr, main_table_entry), log_entry) =~=
           Some(update_bytes(apply_physical_log_entry(penultimate_mem, log_entry).unwrap(), addr, main_table_entry)));
}                

pub proof fn lemma_if_memories_differ_in_free_main_table_entry_their_differences_commute_with_log_replay(
    mem1: Seq<u8>,
    mem2: Seq<u8>,
    op_log: Seq<AbstractPhysicalOpLogEntry>,
    free_indices: Set<u64>,
    free_index: u64,
    overall_metadata: OverallMetadata,
)
    requires
        log_entries_do_not_modify_free_main_table_entries(op_log, free_indices, overall_metadata),
        free_indices.contains(free_index),
        apply_physical_log_entries(mem1, op_log) is Some,
        mem1.len() == mem2.len(),
        0 <= free_index < overall_metadata.num_keys,
        mem1.len() >= overall_metadata.main_table_addr + overall_metadata.main_table_size,
        overall_metadata.main_table_size >= index_to_offset(overall_metadata.num_keys as nat,
                                                           overall_metadata.main_table_entry_size as nat),
        forall|addr: int| {
            let start =
                overall_metadata.main_table_addr +
                index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
            let len = overall_metadata.main_table_entry_size;
            &&& #[trigger] trigger_addr(addr)
            &&& overall_metadata.main_table_addr <= addr
                < overall_metadata.main_table_addr + overall_metadata.main_table_size
            &&& !(start <= addr < start + len)
        } ==> mem1[addr] == mem2[addr]
    ensures
        apply_physical_log_entries(mem2, op_log) is Some,
        ({
            let mem1_post = apply_physical_log_entries(mem1, op_log).unwrap();
            let mem2_post = apply_physical_log_entries(mem2, op_log).unwrap();
            &&& mem1_post.len() == mem2_post.len() == mem1.len()
            &&& forall|addr: int| {
                    &&& #[trigger] trigger_addr(addr)
                    &&& overall_metadata.main_table_addr <= addr
                        < overall_metadata.main_table_addr + overall_metadata.main_table_size
                } ==> {
                    let start = overall_metadata.main_table_addr +
                                index_to_offset(free_index as nat, overall_metadata.main_table_entry_size as nat);
                    let len = overall_metadata.main_table_entry_size;
                    mem2_post[addr] == if start <= addr < start + len { mem2[addr] } else { mem1_post[addr] }
                }
        }),
    decreases
        op_log.len()
{
    if op_log.len() == 0 {
        return;
    }

    lemma_if_memories_differ_in_free_main_table_entry_their_differences_commute_with_log_replay(
        mem1, mem2, op_log.drop_last(), free_indices, free_index, overall_metadata
    );
    lemma_auto_addr_in_entry_divided_by_entry_size(free_index as nat, overall_metadata.num_keys as nat,
                                                   overall_metadata.main_table_entry_size as nat);
}                

pub proof fn lemma_log_replay_preserves_size(
    mem: Seq<u8>, 
    phys_log: Seq<AbstractPhysicalOpLogEntry>, 
) 
    requires
        apply_physical_log_entries(mem, phys_log) is Some 
    ensures
        ({ 
            let replay_mem = apply_physical_log_entries(mem, phys_log).unwrap();
            replay_mem.len() == mem.len()
        })
    decreases phys_log.len()
{
    if phys_log.len() == 0 {
        // trivial
    } else {
        lemma_log_replay_preserves_size(mem, phys_log.subrange(0, phys_log.len() - 1));
    }
}

// This lemma proves that replaying a log of valid entries will always result in a Some return value
pub proof fn lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
    mem: Seq<u8>, 
    version_metadata: VersionMetadata,
    overall_metadata: OverallMetadata,
    phys_log: Seq<AbstractPhysicalOpLogEntry>, 
)
    requires 
        AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
        mem.len() == overall_metadata.region_size,
        overall_metadata.log_area_size <= mem.len(),
    ensures 
        apply_physical_log_entries(mem, phys_log) is Some,
    decreases phys_log.len()
{
    if phys_log.len() == 0 {
        // trivial -- empty log always returns Some
    } else {
        let prefix = phys_log.subrange(0, phys_log.len() - 1);
        let last_op = phys_log[phys_log.len() - 1];
        lemma_apply_phys_log_entries_succeeds_if_log_ops_are_well_formed(
            mem,
            version_metadata,
            overall_metadata,
            phys_log.subrange(0, phys_log.len() - 1),
        );
        lemma_log_replay_preserves_size(mem, prefix);
    }
}

pub open spec fn addr_modified_by_recovery(
    log: Seq<AbstractPhysicalOpLogEntry>,
    addr: int,
) -> bool
{
    exists |j: int| 0 <= j < log.len() &&
        (#[trigger] log[j]).absolute_addr <= addr < log[j].absolute_addr + log[j].bytes.len()
}

pub proof fn lemma_byte_unchanged_by_log_replay(
    addr: int,
    mem: Seq<u8>, 
    version_metadata: VersionMetadata,
    overall_metadata: OverallMetadata,
    op_log: Seq<AbstractPhysicalOpLogEntry>,
)
    requires 
        mem.len() == overall_metadata.region_size,
        overall_metadata.log_area_size <= mem.len(),
        AbstractPhysicalOpLogEntry::log_inv(op_log, version_metadata, overall_metadata),
        apply_physical_log_entries(mem, op_log) is Some,
        !addr_modified_by_recovery(op_log, addr),
        0 <= addr < mem.len(),
    ensures 
        ({
            let mem_with_log_installed = apply_physical_log_entries(mem, op_log).unwrap();
            mem_with_log_installed[addr] == mem[addr] 
        })
    decreases op_log.len()
{
    if op_log.len() == 0 {
        // trivial
    } else {
        let prefix = op_log.subrange(0, op_log.len() - 1);
        let last_op = op_log[op_log.len() - 1];
        let mem_with_prefix = apply_physical_log_entries(mem, prefix).unwrap();
        lemma_log_replay_preserves_size(mem, prefix);
        lemma_byte_unchanged_by_log_replay(addr, mem, version_metadata, overall_metadata, prefix);
    }
}

pub proof fn lemma_mem_equal_after_recovery(
    mem1: Seq<u8>, 
    mem2: Seq<u8>,
    version_metadata: VersionMetadata,
    overall_metadata: OverallMetadata,
    phys_log: Seq<AbstractPhysicalOpLogEntry>, 
)
    requires
        mem1.len() == mem2.len(),
        mem1.len() == overall_metadata.region_size,
        apply_physical_log_entries(mem1, phys_log) is Some,
        apply_physical_log_entries(mem2, phys_log) is Some,
        AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
        forall |i: int| 0 <= i < mem1.len() && mem1[i] != mem2[i] ==> addr_modified_by_recovery(phys_log, i),
    ensures
        ({
            let replay1 = apply_physical_log_entries(mem1, phys_log).unwrap();
            let replay2 = apply_physical_log_entries(mem2, phys_log).unwrap();
            replay1 == replay2
        })
    decreases phys_log.len()
{
    let replay1 = apply_physical_log_entries(mem1, phys_log).unwrap();
    let replay2 = apply_physical_log_entries(mem2, phys_log).unwrap();

    lemma_log_replay_preserves_size(mem1, phys_log);
    lemma_log_replay_preserves_size(mem2, phys_log);

    assert_seqs_equal!(replay1 == replay2, addr => {
        lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, phys_log);
    });
}

pub proof fn lemma_byte_equal_after_recovery_specific_byte(
    addr: int,
    mem1: Seq<u8>, 
    mem2: Seq<u8>,
    version_metadata: VersionMetadata,
    overall_metadata: OverallMetadata,
    phys_log: Seq<AbstractPhysicalOpLogEntry>,
)
    requires
        mem1.len() == mem2.len(),
        mem1.len() == overall_metadata.region_size,
        apply_physical_log_entries(mem1, phys_log) is Some,
        apply_physical_log_entries(mem2, phys_log) is Some,
        AbstractPhysicalOpLogEntry::log_inv(phys_log, version_metadata, overall_metadata),
        mem1[addr] == mem2[addr] || addr_modified_by_recovery(phys_log, addr),
        0 <= addr < mem1.len(),
    ensures
        ({
            let replay1 = apply_physical_log_entries(mem1, phys_log).unwrap();
            let replay2 = apply_physical_log_entries(mem2, phys_log).unwrap();
            replay1[addr] == replay2[addr]
        })
    decreases phys_log.len()
{
    if phys_log.len() == 0 {
        // trivial
    } else {
        let prefix = phys_log.subrange(0, phys_log.len() - 1);
        let last_op = phys_log[phys_log.len() - 1];
        let mem1_with_prefix = apply_physical_log_entries(mem1, prefix).unwrap();
        let mem2_with_prefix = apply_physical_log_entries(mem2, prefix).unwrap();
        lemma_log_replay_preserves_size(mem1, prefix);
        lemma_log_replay_preserves_size(mem2, prefix);

        if mem1[addr] == mem2[addr] || addr_modified_by_recovery(prefix, addr)  {
            lemma_byte_equal_after_recovery_specific_byte(addr, mem1, mem2, version_metadata, overall_metadata, prefix);
        } else if (mem1_with_prefix[addr] != mem2_with_prefix[addr]) {
            // According to the definition of addr_modified_by_recovery, there exists a log entry
            // in phys_log that modifies this address. We have proven that the log entry cannot be 
            // in prefix.Verus can easily prove that applying the log entry that modifies the address 
            // will make the byte match in both mems, but we have to convince it that it must be 
            // the last op by proving that this is the only op that is not in the prefix.
            assert(forall |i: int| 0 <= i < prefix.len() ==> prefix[i] == phys_log[i]);
        }
        // else, trivial
    }
}

}
