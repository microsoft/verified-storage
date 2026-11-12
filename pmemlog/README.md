# About

This directory contains the Verus code for a persistent-memory append-only
log

## Table of contents
1. [Setup](#setup-instructions)
2. [Verification](#verification)

### Setup instructions

1. Clone Verus, from `https://github.com/verus-lang/verus`, as a sibling
   `verus` of this `verified-storage` repo.
2. If you want to use the exact Verus repo commit that we last verified this
   project with, run `git checkout 9ab45f5745cea3f82b89bb53ff6fd91c14ae6eda`
   from the `verus` directory.
3. Build Verus.

### Verification

To verify the log:
1. Make sure Verus (usually in `~/.cargo/bin/`) is in your `PATH`.
2. From the top-level directory of this repository, `cd` to `pmemlog` and run `cargo verus verify`.
