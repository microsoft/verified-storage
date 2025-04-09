// This file provides functions for recovering objects, corruption-detecting Booleans (CDB), and byte sequences from persistent memory regions.
// It includes both specification and executable functions for recovery operations with CRC validation.

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::seq::*;
use crate::pmem::pmemspec_t::*;
use crate::pmem::pmcopy_t::*;
use crate::pmem::traits_t::{size_of, PmSized, ConstPmSized, UnsafeSpecPmSized, PmSafe};
use crate::pmem::pmemutil_v::*;
use super::subrange_v::*;

verus! {

/// Recovers an object of type T from a sequence of bytes, verifying its CRC.
/// Returns Some(T) if recovery is successful, otherwise None.
pub open spec fn recover_object<T>(s: Seq<u8>, start: int, crc_addr: int) -> Option<T>
    where
        T: PmCopy
{
    if {
        &&& 0 <= start
        &&& start + T::spec_size_of() <= s.len()
        &&& 0 <= crc_addr
        &&& crc_addr + u64::spec_size_of() <= s.len()
    } {
        let object_bytes = extract_section(s, start, T::spec_size_of());
        let crc_bytes = extract_section(s, crc_addr, u64::spec_size_of());
        if {
            &&& T::bytes_parseable(object_bytes)
            &&& u64::bytes_parseable(crc_bytes)
            &&& crc_bytes == spec_crc_bytes(object_bytes)
        } {
            Some(T::spec_from_bytes(object_bytes))
        }
        else {
            None
        }
    }
    else {
        None
    }
}

/// Recovers a corruption-detecting Boolean (CDB) from a sequence of bytes.
/// Returns Some(true) or Some(false) if recovery is successful, otherwise None.
pub open spec fn recover_cdb(s: Seq<u8>, addr: int) -> Option<bool>
{
    if 0 <= addr && addr + u64::spec_size_of() <= s.len() {
        let cdb_bytes = extract_section(s, addr, u64::spec_size_of());
        if u64::bytes_parseable(cdb_bytes) {
            let cdb = u64::spec_from_bytes(cdb_bytes);
            if cdb == CDB_FALSE {
                Some(false)
            } else if cdb == CDB_TRUE {
                Some(true)
            } else {
                None
            }
        }
        else {
            None
        }
    }
    else {
        None
    }
}

/// Recovers a sequence of bytes from a given start position and length, verifying its CRC.
/// Returns Some(Seq<u8>) if recovery is successful, otherwise None.
pub open spec fn recover_bytes(s: Seq<u8>, start: int, num_bytes: nat, crc_addr: int) -> Option<Seq<u8>>
{
    if {
        &&& 0 <= start
        &&& start + num_bytes <= s.len()
        &&& 0 <= crc_addr
        &&& crc_addr + u64::spec_size_of() <= s.len()
    } {
        let bytes = extract_section(s, start, num_bytes);
        let crc_bytes = extract_section(s, crc_addr, u64::spec_size_of());
        if {
            &&& u64::bytes_parseable(crc_bytes)
            &&& crc_bytes == spec_crc_bytes(bytes)
        } {
            Some(bytes)
        }
        else {
            None
        }
    }
    else {
        None
    }
}

/// Executes the recovery of an object of type T from persistent memory, verifying its CRC.
/// Returns Some(T) if recovery is successful, otherwise None.
/// If it returns None, it guarantees that the underlying persistent memory was corrupted.
pub exec fn exec_recover_object<PM, T>(pm: &PM, start: u64, crc_addr: u64) -> (result: Option<T>)
    where
        PM: PersistentMemoryRegion,
        T: PmCopy,
    requires
        pm.inv(),
        recover_object::<T>(pm@.read_state, start as int, crc_addr as int) is Some,
        crc_addr + u64::spec_size_of() <= start || start + T::spec_size_of() <= crc_addr, // object doesn't overlap CRC
    ensures
        match result {
            None => !pm.constants().impervious_to_corruption(),
            Some(x) => recover_object::<T>(pm@.read_state, start as int, crc_addr as int) == Some(x),
        },
{
    let ghost true_bytes = extract_section(pm@.read_state, start as int, T::spec_size_of());
    let ghost true_x = T::spec_from_bytes(true_bytes);
    let maybe_corrupted_x = match pm.read_aligned::<T>(start) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; },
    };
    let maybe_corrupted_crc = match pm.read_aligned::<u64>(crc_addr) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; },
    };

    if check_crc(maybe_corrupted_x.as_slice(), maybe_corrupted_crc.as_slice(),
                 Ghost(true_bytes), Ghost(pm.constants()), Ghost(start as int), Ghost(crc_addr as int)) {
        Some(*maybe_corrupted_x.extract_init_val(Ghost(true_x)))
    }
    else {
        None
    }
}

/// Executes the recovery of a corruption-detecting Boolean (CDB) from persistent memory.
/// Returns Some(true) or Some(false) if recovery is successful, otherwise None.
/// If it returns None, it guarantees that the underlying persistent memory was corrupted.
pub exec fn exec_recover_cdb<PM>(pm: &PM, addr: u64) -> (result: Option<bool>)
    where
        PM: PersistentMemoryRegion,
    requires
        pm.inv(),
        recover_cdb(pm@.read_state, addr as int) is Some,
    ensures
        match result {
            None => !pm.constants().impervious_to_corruption(),
            Some(b) => recover_cdb(pm@.read_state, addr as int) == Some(b),
        },
{
    let ghost true_bytes = extract_section(pm@.read_state, addr as int, u64::spec_size_of());
    let maybe_corrupted_bytes = match pm.read_aligned::<u64>(addr) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; },
    };

    check_cdb(maybe_corrupted_bytes, Ghost(true_bytes), Ghost(pm.constants()), Ghost(addr as int))
}

/// Executes the recovery of a sequence of bytes from persistent memory, verifying its CRC.
/// Returns Some(Vec<u8>) if recovery is successful, otherwise None.
/// If it returns None, it guarantees that the underlying persistent memory was corrupted.
pub exec fn exec_recover_bytes<PM>(pm: &PM, start: u64, num_bytes: u64, crc_addr: u64) -> (result: Option<Vec<u8>>)
    where
        PM: PersistentMemoryRegion,
    requires
        pm.inv(),
        recover_bytes(pm@.read_state, start as int, num_bytes as nat, crc_addr as int) is Some,
        crc_addr + u64::spec_size_of() <= start || start + num_bytes <= crc_addr, // bytes don't overlap CRC
    ensures
        match result {
            None => !pm.constants().impervious_to_corruption(),
            Some(s) => s@ == recover_bytes(pm@.read_state, start as int, num_bytes as nat, crc_addr as int).unwrap(),
        },
{
    let ghost true_bytes = extract_section(pm@.read_state, start as int, num_bytes as nat);
    let maybe_corrupted_bytes = match pm.read_unaligned(start, num_bytes) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; },
    };
    let maybe_corrupted_crc = match pm.read_aligned::<u64>(crc_addr) {
        Ok(bytes) => bytes,
        Err(_) => { assert(false); return None; },
    };

    if check_crc(maybe_corrupted_bytes.as_slice(), maybe_corrupted_crc.as_slice(),
                 Ghost(true_bytes), Ghost(pm.constants()), Ghost(start as int), Ghost(crc_addr as int)) {
        Some(maybe_corrupted_bytes)
    }
    else {
        None
    }
}

pub open spec fn seq_option_to_option_seq<T>(s: Seq<Option<T>>) -> Option<Seq<T>>
{
    if forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] is Some {
        Some(Seq::<T>::new(s.len(), |i: int| s[i].unwrap()))
    }
    else {
        None
    }
}

}

