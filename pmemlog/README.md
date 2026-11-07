# About

This directory contains the Verus code for a persistent-memory append-only
log

## Table of contents
1. [Setup](#setup-instructions)
2. [Verification](#verification)

### Setup instructions

Clone Verus, from `https://github.com/verus-lang/verus`, as a sibling `verus` of this `verified-storage` repo. Build it.

### Verification

To verify the log:
1. Make sure Verus (usually in `~/.cargo/bin/`) is in your `PATH`.
2. From the top-level directory of this repository, `cd` to `pmemlog` and run `cargo verus verify`.
