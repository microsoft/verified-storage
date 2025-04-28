use builtin::*;
use builtin_macros::*;
use crate::pmem::pmemspec_t::*;
use deps_hack::PmCopy;
use vstd::prelude::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::*;
use crate::nat_seq_max;

verus! {
    #[derive(Copy, Clone)]
    pub enum EntryStatus 
    {
        // the entry was created in this transaction.
        // entries retain this state if they are subsequently
        // updated (but not deleted) in the same transaction
        Created, 
        // the entry existed prior to the transaction and was 
        // updated in this transaction.
        Updated,
        // the entry existed prior to this transaction and 
        // was deleted in this transaction
        Deleted,
        // the entry was both created and deleted in this
        // transaction
        CreatedThenDeleted,
    }

    pub open spec fn index_to_offset(index: nat, entry_size: nat) -> nat 
    {
        index * entry_size
    }

    pub open spec fn outstanding_bytes_match(pm: PersistentMemoryRegionView, start: int, bytes: Seq<u8>) -> bool
    {
        forall|addr: int| start <= addr < start + bytes.len() ==>
            #[trigger] pm.read_state[addr] == bytes[addr - start]
    }

    pub proof fn lemma_outstanding_bytes_match_after_flush(pm: PersistentMemoryRegionView, start: int, bytes: Seq<u8>)
        requires 
            0 <= start <= start + bytes.len() <= pm.len(),
            outstanding_bytes_match(pm, start, bytes),
        ensures 
            extract_bytes(pm.read_state, start as nat, bytes.len()) == bytes
    {
        assert(extract_bytes(pm.read_state, start as nat, bytes.len()) =~= bytes);
    }

    // This lemma proves that an index that is less than num_keys (i.e., within bounds of the table) 
    // represents a valid table entry that we can read and parse.

    pub proof fn lemma_valid_entry_index(index: nat, num_keys: nat, size: nat)
        ensures 
            (index + 1) * size == index * size + size,
            index < num_keys ==> index * size + size <= num_keys * size
    {
        if index < num_keys {
            vstd::arithmetic::mul::lemma_mul_inequality(index + 1 as int, num_keys as int, size as int);
        }
        vstd::arithmetic::mul::lemma_mul_basics(size as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, index as int, 1);
    }

    // This lemma proves that an index that is less than num_keys (i.e., within bounds of the table) 
    // represents a valid table entry that we can read and parse.

    pub proof fn lemma_entries_dont_overlap_unless_same_index(index1: nat, index2: nat, size: nat)
        ensures
            index1 < index2 ==> (index1 + 1) * size <= index2 * size,
            index1 > index2 ==> (index2 + 1) * size <= index1 * size,
            (index1 + 1) * size == index1 * size + size,
            (index2 + 1) * size == index2 * size + size,
    {
        if index1 < index2 {
            vstd::arithmetic::mul::lemma_mul_inequality(index1 + 1 as int, index2 as int, size as int);
        }

        if index1 > index2 {
            vstd::arithmetic::mul::lemma_mul_inequality(index2 + 1 as int, index1 as int, size as int);
        }

        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, index1 as int, 1);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(size as int, index2 as int, 1);
    }

    pub proof fn lemma_addr_in_entry_divided_by_entry_size(index: nat, size: nat, addr: int)
        requires
            index * size <= addr < index * size + size,
        ensures
            addr / size as int == index,
    {
        let r = addr - index * size;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(addr, size as int, index as int, r as int);
    }

    pub open spec fn trigger_addr(addr: int) -> bool
    {
        true
    }

    pub proof fn lemma_auto_addr_in_entry_divided_by_entry_size(index: nat, num_entries: nat, entry_size: nat)
        requires
            entry_size > 0,
        ensures
            num_entries * entry_size == entry_size * num_entries,
            (index + 1) * entry_size == index * entry_size + entry_size,
            index < num_entries ==> index * entry_size + entry_size <= num_entries * entry_size,
            forall|addr: int| #[trigger] trigger_addr(addr) && 0 <= addr ==> {
                let i = addr / entry_size as int;
                &&& 0 <= i
                &&& addr < num_entries * entry_size <==> i < num_entries
                &&& i * entry_size <= addr < i * entry_size + entry_size
                &&& i == index <==> index * entry_size <= addr < index * entry_size + entry_size
                &&& (i + 1) * entry_size == i * entry_size + entry_size
            },
    {
        lemma_valid_entry_index(index, num_entries, entry_size);
        assert forall|addr: int| #[trigger] trigger_addr(addr) && 0 <= addr implies {
            let i = addr / entry_size as int;
            &&& 0 <= i
            &&& addr < num_entries * entry_size <==> i < num_entries
            &&& i * entry_size <= addr < i * entry_size + entry_size
            &&& i == index <==> index * entry_size <= addr < index * entry_size + entry_size
            &&& (i + 1) * entry_size == i * entry_size + entry_size
        } by {
            let i = addr / entry_size as int;
            assert(index_to_offset(i as nat, entry_size as nat) + addr % entry_size as int == addr) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(addr, entry_size as int);
                vstd::arithmetic::mul::lemma_mul_is_commutative(addr / entry_size as int, entry_size as int);
            }
            if i >= num_entries {
                vstd::arithmetic::mul::lemma_mul_inequality(num_entries as int, i, entry_size as int);
            }
            lemma_valid_entry_index(i as nat, num_entries as nat, entry_size as nat);
            lemma_entries_dont_overlap_unless_same_index(i as nat, index as nat, entry_size as nat);
        }
    }

}
