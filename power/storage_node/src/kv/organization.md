# KV file organization

This document describes the organization of the `kv` module.

At the top level of the `kv` module is the specification and implementation of the KV store itself. It also has two submodules, `durable` and `volatile`, which are described in more detail below.

Most modules, particularly those for durable components, are organized roughly as follows. Each module contains:
- a verified implementation file `*impl_v.rs`, in which the key functionality of the module is implemented.
-  a specification file `*spec_t.rs` containing the specification for the component defined in the module. Most of these specs are not trusted, so their files should be renamed.
- a `layout_v.rs` file containing definitions of durable structures, spec functions for manipuating these structures, and usually a spec function describing how to parse the component's durable layout.
- an `inv_v.rs` containing proofs and sometimes spec functions about that particular component/module only.

As the system grows larger, we'll probably split out some code from `*impl_v.rs` files into separate files, as was done for the logs with `start`/`setup`/`append` functionality.


## Top-level KV store module
The top-level KV store code is organized as follows.
- `inv_v.rs` contains lemmas about the state of the top-level KV store.
- `kvimpl_t.rs` contains the trusted interface to the KV store. This is also where the `KvError` enum that the KV store uses as the error type in most returned `Result` is defined.
- `kvimpl_v.rs` contains the verified implementation of the KV store. The trusted interface functions are wrappers for most of the untrusted functions in this file. This file also contains an (incomplete) specification for KV store recovery.
- `kvspec_t.rs` contains the trusted specification of the top-level KV store as an `AbstractKvStoreState`. This spec describes the state of the entire KV store (i.e. both volatile and durable state together). This spec is pretty simple -- it maps each key to a tuple containing an item and a sequence of list elements. It currently contains a specification of each operation that the KV store will support, although some may be out of date.
- `setup_v.rs` contains spec functions and exec code describing how the KV store's global metadata is set up and stored.

## `durable` module
The `durable` module contains four submodules (one for each main durable component) as well as a top-level interface implementation and specification.

### Top-level `durable` implementation and specification
- `durableimpl_v.rs` contains verified implementations of functions that will be called by the top-level key-value store to perform operations on durable state. These functions hide the internal separation of PM into different subregions. It also includes spec functions definining physical and logical log recovery and and an `inv` function on the top-level durable state.
- `durablespec_t.rs` contains an incomplete specification of operations on the top-level durable state. It represents this state as a map from integer indexes in the main table to `DurableKvStoreViewEntry`s, which contain the key, item, and list associated with the main table index. This specification corresponds to the interface presented by the top-level durable implementation, which uses main table indexes to look up records.
- `inv_v.rs` contains proof and spec functions to help verify the functions in `durableimpl_v.rs`.
- `util_v.rs` contains the definition of the `DurableEntry` enum, which we use to indicate whether a durable entry (in any component) is invalid (record CDB is false and we have no tentative updates to the record), valid (record CDB is true), or tentative (record CDB is false and we have tentative updates to the record), plus some helper functions. This should potentially be mvoed to `durablespec_t.rs`, since it will be used only in views of durable components.


### `durablelist` module
This module contains code for managing list values and the persistent list area.
- `durablelistimpl_v.rs` contains spec functions dealing with list recovery, some related proof functions, and implementations of the main operations performed by the top-level durable module. Currently, many of these operations have unverified and out-of-date inmplementations.
- `durablelistspec_t.rs` contains the specification for the durable list in the `DurableListView` type. The view is structured as a sequence of list entries and maintains two versions of list state: the durable view (`durable_lists` field), which represents the current state of the system with all committed operations applied, and the tentative view (`tentative_lists` field) which represents the state of the system with any pending operations copmleted. This spec is currently extremely minimal and does not include specs for most list operations.
- `layout_v.rs` contains the `parse_list_node` spec function and not much else. The list area contains user-defined structures as list elements and does not store its own metadata, so there isn't much we need to do here to handle internal durable structures.

### `itemtable` module
This module contains code for managing the item table.
- `itemtableimpl_v.rs` contains spec functions dealing with recovery, some related proof functions, and implementations of the main operations performed by the top-level durable module. It also contains the definition of `DurableItemTable`, which stores in volatile memory some metadata about the item table, a free list used as an allocator, and the ghost state of the table.
- `itemtablespec_t.rs` contains the specification for the item table in the `DurableItemTableView` type. Like the list view, the item table view contains a durable and a tentative sequence of `DurableEntry`s each representing one slot in the item table. This spec is also quite minimal at the moment.
- `layout_v.rs` describes the persistent layout of the item table. Again, this is mostly done with a `parse_item_table` function and some related helpers, since item table entries contain user-defined types and the item table doesn't maintain its own metadata.

### `metadata` module
This module contains code for managing the main table where keys and the location of corresponding items and lists are stored. At some point this module should be renamed to reflect the change in terminology from "metadata table" to "main table".
- `metadataimpl_v.rs` contains spec functions for dealing with recoveryr and ipmlementations of the main operations performed on the main table by the top-level durable module. It also contains the definition of the `MetadataTable` type, which stores a ghost state and a free list used as an allocator for slots in the table.
- `metadataspec_t.rs` contains the specification of the main table, also structured with a durable and tentative version. This spec is also quite minimal currently.
- `layout_v.rs` contains the definition of `ListEntryMetadata`, the internal type used to store record metadata in the main table. It also has spec functions to validate and parse the main table and some related proofs.

### `oplog` module
The `oplog` module is essentially a wrapper around the single log to provie slightly richer semantics/more useful operations in the context of the KV store.
- `oplogimpl_v.rs` contains spec/proof functions dealing with log recovery and exec functions that will be called by the top-level durable KV store to append to, read, and clear the log.
- `oplogspec_t.rs` contains a somewhat minimal specification of the op log as a list of log entries.
- `inv_v.rs` doesn't contain anything useful and can probably be deleted if we don't end up putting any proofs or untrusted spec functions in it.