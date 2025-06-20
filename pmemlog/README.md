# About

This directory contains the Verus code for a persistent-memory append-only
log

## Table of contents
1. [Setup](#setup-instructions)
2. [Verification](#verification)

### Setup instructions

Install Verus from `https://github.com/verus-lang/verus`.

### Verification

To verify the log, run the following.

```
cd pmemlog/src
verus lib.rs --crate-type=lib
```
