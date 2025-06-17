# About

This crate implements a verified persistent-memory key/value store where each
value consists of a fixed-size item plus an appendable list of fixed-size
elements.

# Top-level interface

The top-level interface gives the choice of a non-concurrent key/value store
`KvStore` and a concurrent key/value store `ConcurrentKvStore`. The former is
intended to be used by a single thread that maintains ownership of it; the
latter uses a multiple-readers/single-writer lock to let multiple threads make
concurrent requests.

# UntrustedKvStoreImpl

Most of the code for the key/value store implements `UntrustedKvStoreImpl`,
which, as its name suggests, requires no trust because all of its code is
verified. Its specification uses PoWER to prove that not only are its
operations are correct but that they're also crash-consistent. Higher-level
code creates restrictions that enforce crash consistency, and the untrusted
code conforms to those restrictions.

The interface to `UntrustedKvStoreImpl` is transactional. Its API consists of
containing `abort`, `commit`, various read-only operations, and various
tentative operations that are made durable atomically at the subsequent
`commit`. It also implements `space_needed_for_setup`, which indicates the
size of persistent memory needed; `setup`, which stores an initial empty state
on persistent memory; and `start`, which recovers state from persistent memory
and from that creates an `UntrustedKvStoreImpl`.

The implementation of `UntrustedKvStoreImpl` uses three main components:

- `KeyTable` (in directory `keys`) maps each key to an item index and a list index.
   The latter is zero if the key's value has no elements.
- `ItemTable` (in directory `items`) maps each item index to an item.
- `ListTable` (in directory `lists`) maps each nonzero list index to a list of elements.

Each of these components uses a fixed-size subregion of the persistent memory region
assigned to the key/value store. It stores its data as a table of fixed-size entries,
and treats unused entries as part of a free list.

Operations supported by the key/value store are as follows:

- `read_item` returns the item associated with a key.
- `read_list` returns the list of elements associated with a key.
- `read_item_and_list` returns the item and list associated with a key.
- `get_list_length` returns the number of elements in the list associated with a key.
- `get_keys` returns a list of all the keys in the store.
- `tentatively_create` creates a new key and associates it with an item and an empty
   list. Like all mutating operations, it is done tentatively, meaning that it is
   seen by subsequent reads but not made durable until the next `commit` operation.
- `tentatively_update_item` updates the item associated with a key.
- `tentatively_append_to_list` appends an element to the list associated with a key.
- `tentatively_delete` deletes a key and its associated item and list.
- `tentatively_trim_list` trims the list associated with a key by removing the
   given number of elements from the beginning of that list.
- `tentatively_update_list_element_at_index` updates the list associated with a
   given key at a given index, replacing the element at that position with the
   given new one.
- `tentatively_append_to_list_and_update_item` both appends an element to the list
   associated with a key and updates the item associated with that key. (One could
   do this with separate calls to `tentatively_append_to_list` and
   `tentatively_update_item`, which would be equivalent due to the transactional
   nature of the API, but this combined function is more efficient.)
- `tentatively_update_list_element_at_index_and_item` combines the effects of
   `tentatively_update_list_element_at_index` and `tentatively_update_item`.
- `tentatively_trim_list_and_update_item` combines the effects of
   `tentatively_trim_list` and `tentatively_update_item`.

# List elements

The list element type `L` is specified at setup time. It must be
persistent-memory safe, i.e., if copied to persistent memory and restored
after a crash there should be no loss of meaning (e.g., it can't contain
object references or file handles). We enforce this by requiring it to be
declared with `#[derive(PmCopy)]`, which will raise a compile-time error if it
contains anything other than signed or unsigned fixed-size integers, and
arbitrarily nested `struct`s and `enum`s thereof.

The list element should also implement the `LogicalRange` trait, having
`start` and `end` functions that return the logical start and end of the
element, each as a `usize`. The key/value store will then enforce that
elements are appended to each key's list in logical-range order, i.e., the
start of an appended element must be at least as large as the end of the last
element of the key's list. At setup time, one can set a more stringent policy
that there are no gaps between consecutive elements. If one doesn't care about
logical range enforcement, one can simply have the `start` and `end` functions
both always return 0.

# Usage

The file `../testkv_v.rs` contains examples of usage of the non-concurrent
`KvStore` and the concurrent `ConcurrentKvStore`. For instance, here is some
code to use `KvStore` on a memory-mapped file:

```
pub fn test_kv_on_memory_mapped_file() -> Result<(), ()>
{
    let kv_file_name = "test_kv";

    let max_keys = 16;
    let max_list_elements = 16;

    // delete the test file if it already exists. Ignore the result,
    // since it's ok if the file doesn't exist.
    remove_file(kv_file_name);

    let kvstore_id = generate_fresh_id();

    let ps = SetupParameters{
        kvstore_id,
        logical_range_gaps_policy: LogicalRangeGapsPolicy::LogicalRangeGapsForbidden,
        max_keys,
        max_list_elements,
        max_operations_per_transaction: 4,
    };
   let region_size = match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>
        ::space_needed_for_setup(&ps) {
        Ok(s) => s,
        Err(e) => { print_message("Failed to compute space needed for setup"); return Err(()); },
   };

    let mut pm = match create_pm_region(&kv_file_name, region_size) {
        Ok(p) => p,
        Err(e) => { print_message("Failed to create file for kv store"); return Err(()); },
    };

    assume(vstd::std_specs::hash::obeys_key_model::<TestKey>());
    match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>::setup(&mut pm, &ps) {
        Ok(()) => {},
        Err(e) => { print_message("Failed to set up KV store"); return Err(()); },
    }

    let mut kv = match KvStore::<FileBackedPersistentMemoryRegion, TestKey, TestItem, TestListElement>
        ::start(pm, kvstore_id) {
        Ok(kv) => kv,
        Err(e) => { print_message("Failed to start KV store"); return Err(()); },
    };

    let key1 = TestKey { val: 0x33333333 };
    let key2 = TestKey { val: 0x44444444 };

    let item1 = TestItem { val: 0x55555555 };
    let item2 = TestItem { val: 0x66666666 };

    // create a record
    match kv.tentatively_create(&key1, &item1) {
        Ok(()) => {},
        Err(e) => { print_message("Error when creating key 1"); return Err(()); }
    }
    match kv.commit() {
        Ok(()) => { },
        Err(e) => { print_message("Error when committing"); return Err(()); }
    }

    // read the item of the record we just created
    let read_item1 = match kv.read_item(&key1) {
        Ok(i) => i,
        Err(e) => { print_message("Error when reading key"); return Err(()); },
    };

    runtime_assert(read_item1.val == item1.val);

    match kv.read_item(&key2) {
        Ok(i) => { print_message("Error: failed to fail when reading non-inserted key"); return Err(()); },
        Err(KvError::KeyNotFound) => {},
        Err(e) => { print_message("Error: got an unexpected error when reading non-inserted key"); return Err(()); },
    }

    print_message("All kv operations gave expected results");
    return Ok(());
}
```
