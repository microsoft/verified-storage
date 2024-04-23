# Verified key-value store

## Overview 

The `storage_node` crate contains a verified persistent-memory key value store. It contains the following submodules:

* `pmem`: a specification of how persistent memory is assumed to behave, including both normal operation and exceptional cases like crashes and bit corruiption. This submodule also contains a mock of persistent memory using volatile memory and implementations of the PM interface for use on Linux with a DAX-supported file system and on Winows.
* `multilog`: a verified implementation of a "multilog", a structure that stores multiple circular logs on persistent memory and provides crash-atomic appends to multiple logs at a time. More documentation on the multilog can be found in its [README](multilog/README.md).
* `kv`: a verified implementation of a crash-consistent, byte-corruption-resistent persistent memory key-value store. 

## Verifying, building, and running the code

To verify, build, and run the code, follow the following steps.

1. Install [Verus](https://github.com/verus-lang/verus) if you don't already have it.

2. Build the `deps_hack` crate if you haven't yet done so, with:
```
cd deps_hack
cargo build
```

3. Verify the code with:
```
verus --crate-type=lib -L dependency=../deps_hack/target/debug/deps --extern=deps_hack=../deps_hack/target/debug/libdeps_hack.rlib src/lib.rs
```
Alternatively, set the `VERUS_PATH` variable in `verify.sh` to point to your local Verus installation, and run `./verify.sh`. 

It should report 0 verification errors.