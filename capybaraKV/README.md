# About

This directory contains the current version of the verified key-value store
called CapybaraKV. An earlier version was described in the OSDI 2025 paper
"PoWER Never Corrupts: Tool-Agnostic Verification of Crash Consistency and
Corruption Detection" by Hayley LeBlanc, Jacob R. Lorch, Chris Hawblitzel,
Cheng Huang, Yiheng Tao, Nickolai Zeldovich, and Vijay Chidambaram. You can
find that earlier version in the artifact for that paper, available on this
repo in the `osdi25-artifact` branch.

## Table of contents
1. [Setup](#setup-instructions)
2. [Verification](#verification)
3. [Computing code size](#computing-code-size)
4. [Manual auditing](#manual-auditing)

### Setup instructions

1. Install Verus from `https://github.com/verus-lang/verus`.
2. If you want to do line counting, run `cargo install tokei` and `pip install prettytable`.
3. **Optional**: If you are on Linux (or WSL2) and would like to run CapybaraKV on (real or emulated) PM via Linux's DAX feature, run the following to install PMDK to access PM and LLVM/Clang to generate Rust bindings to PMDK: `sudo apt install libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev llvm-dev clang libclang-dev`

### Verification

To verify CapybaraKV, make sure Verus (usually at `verus/source/target-verus/release`) is in your path and run one of the following, depending on your setup:
1. If you are on Linux/WSL and installed the optional dependencies in step 3 above, run: `cargo verus verify`
2. Otherwise, run: `cargo verus verify --no-default-features`

### Compiling for execution

CapybaraKV can be built using `cargo build --no-default-features`. Exclude `--no-default-features` if you installed the dependencies in Setup Step 3 and would like to use real/emulated PM.

### Computing code size

We use Verus's built-in line-counting tool to count lines of code and categorize them as trusted, specification/proof, or executable. 
We provide a python script, `count_capybarakv_lines.py`, that uses this tool to generate a table of line counts and a proof-to-code ratio for CapybaraKV.
The script also uses `tokei` (https://github.com/XAMPPRocky/tokei, installed in the setup instructions above) to count the lines of code in the `pmcopy` crate, which is implemented in regular Rust.

To use the script, run the following commands. These differ from the standard verification instructions because `cargo verus` does not currently support the required options.
1. `cd deps_hack` and run `cargo build --no-default-features`. Omit `--no-default-features` if you installed the dependencies in Setup Step 3. 
2. Run the following:
    ```bash
    cd ../capybarakv/src
    verus lib.rs --compile --expand-errors -L dependency=../../deps_hack/target/debug/deps --extern=deps_hack=../../deps_hack/target/debug/libdeps_hack.rlib --emit=dep-info

    # `path-to-verus-directory` should be the path to the top-level directory in Verus' source code
    python3 count_capybarakv_lines.py lib.d ../../pmcopy <path-to-verus-directory>
    ```
The final command will output a table of line counts for different components of the system and the systems proof-to-code ratio.

### Manual auditing

To gain confidence that what is being verified is indeed a reasonable specification of correctness for a key/value store, you may decide to audit the unverified parts of the code.
All of the files referred to in this section are in `capybarakv/src` except for the `pmcopy` crate, which has its source code in `pmcopy/src`.

The untrusted code, which is verified by Verus, consists of various files ending in `_v.rs`, where the `v` stands for "verified". You don't have to read these files to have confidence in the correctness of the system; you just need to have Verus verify them, as described above. The other code files, i.e., the files ending in `_t.rs`, need to be read and understood to audit the system properly.

The files whose auditing are especially relevant to the main topic of the OSDI 2025 paper are:
* `kv2/impl_t.rs`, the top-level API for CapybaraKV, which shows how one can use the PoWER approach to implement a trusted single-threaded API that ensures crash consistency even though it uses an untrusted verified component;
* `pmem/pmemspec_t.rs`, which has our prophecy-based model of persistent memory;
* `pmem/power_t.rs`, which provides data structures for writing PoWER specifications; and
* `pmem/power_sound_t.rs`, which demonstrates that satisfying a PoWER specification implies the satisfaction of an atomic invariant.

For those interested in auditing all the untrusted files, even those less relevant to the research results, those files fall into two categories: (1) The `pmem` directory contains framework-provided functionality including modeling of persistent memory and the crash and corruption behavior thereof. (2) Trusted Verus files in the `kv2` directory describe the key/value service specification (`spec_t.rs`); the PoWER-based wrapper that ensures crash consistency for the single-threaded version of the service (`impl_t.rs`); and files that specify concurrent versions of the service (`concurrentspec_t.rs`, `rwkv_t.rs`, and `shardkv_t.rs`).

Our design enables the use of the same untrusted verified component for single-threaded and multi-threaded versions, `UntrustedKvStoreImpl`. The single-threaded version, in `kv2/impl_t.rs`, upon startup supplies the `UntrustedKvStoreImpl` with a blanket permission permitting it to do arbitrary mutations to storage as long as they don't affect the post-recovery state. This permission is all that's needed to support all operations except `commit`, since `commit` is the only operation that's permitted to change the post-recovery state. For `commit`, `kv2/impl_t.rs` provides a single-use permission allowing the untrusted KV store to transition from the pre-commit state to the post-commit state.

As discussed in the OSDI 2025 paper, we have a Verus library that exposes the PoWER interface but enforces an atomic invariant about the storage state. This serves two purposes. First, the existence of this library demonstrates that satisfying a PoWER specification implies the satisfaction of an atomic invariant. Second, we can use it to build a KV store satisfying a concurrent specification, leveraging the untrusted component `UntrustedKvStoreImpl` that was designed with a PoWER interface. To audit the first claim, read `pmem/power_sound_t.rs`. To audit the second claim, read the specifications for the concurrent KV stores. These specifications, unlike the one for the single-threaded KV store, do not expose transactions; rather, they describe various read-only and mutating operations that can be done atomically. For each mutating operation, its API has the caller supply a `MutatingLinearizer`, which gives a proof-mode callback to be called by the KV store atomically with the commit point of the operation.

As discussed in the OSDI 2025 paper, we have two concurrent KV stores satisfying the specification in `kv2/concurrent_spec_t`. One, specified in `kv2/rwkv_t.rs`, uses a multiple-readers/single-writer lock to allow concurrent reads but not concurrent writes. The other, specified in `kv2/shardkv_t.rs`, uses sharding by key hash to allow concurrent writes to keys occupying different shards. None of these files needs to be audited for proper use of PoWER since they use PoWER internally, in `_v.rs` files that don't needed to be trusted. That is, they leverage our library to use PoWER to establish an atomic invariant, which is in turn used to call mutating callbacks at provably appropriate times.
