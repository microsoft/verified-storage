# About

This directory contains the Verus code for a persistent-memory append-only
log

## Table of contents
1. [Setup](#setup-instructions)
2. [Verification](#verification)

### Setup instructions

Install Verus from `https://github.com/verus-lang/verus`.

### Verification

To verify the log, `cd` to the `pmemlog/` directory and run the following.
```
cd src
cargo verus verify
```
