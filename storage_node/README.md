# Verified key-value store

## Overview 

The `storage_node` crate contains a verified persistent-memory key value store. It contains the following submodules:

* `pmem`: a specification of how persistent memory is assumed to behave, including both normal operation and exceptional cases like crashes and bit corruiption. This submodule also contains a mock of persistent memory using volatile memory and implementations of the PM interface for use on Linux with a DAX-supported file system and on Winows.
* `multilog`: a verified implementation of a "multilog", a structure that stores multiple circular logs on persistent memory and provides crash-atomic appends to multiple logs at a time. More documentation on the multilog can be found in its [README](multilog/README.md).
* `kv`: a verified implementation of a crash-consistent, byte-corruption-resistent persistent memory key-value store. 

## Verifying, building, and running the code

To verify, build, and run the code, follow the following steps.

1. Install [Verus](https://github.com/verus-lang/verus) if you don't already have it.

2. Build the `pmcopy` crate if you haven't yet done so, with:
```
cd pmcopy
cargo build
```

3. Build the `deps_hack` crate if you haven't yet done so. 
   - If you are running the KV store on Linux, `deps_hack` depends on `bindgen` and several libraries from [PMDK](https://pmem.io/pmdk/). Install the following packages to meet these dependencies: `llvm-dev libclang-dev clang libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev`
   - If you are using Windows, `cargo` will take care of all dependencies.
  
Then, to build `deps_hack`, run:
```
cd deps_hack
cargo build
```

4. Verify the code with:
```
cd storage_node
verus --crate-type=lib --compile -L dependency=../deps_hack/target/debug/deps --extern=deps_hack=../deps_hack/target/debug/libdeps_hack.rlib src/lib.rs
```
Alternatively, set the `VERUS_PATH` variable in `verify.sh` to point to your local Verus installation, and run `./verify.sh`. 
This script also builds `pmcopy` and `deps_hack`.
The `--compile` flag is necessary to perform some non-Verus compile time checks that are part of the verification process. 
Specifically, compile-time assertions, which help check that we use the correct size for structures in proofs, are run by the Rust compiler, not by Verus.

It should report 0 verification errors.
