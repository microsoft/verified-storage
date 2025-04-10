#!/bin/bash

# clear
cd ../../deps_hack
echo "Building deps_hack"
cargo build
cd ../pmcopy
echo "Building pmcopy"
cargo build
cd ../storage_node/src
echo "Verifying"
# The --compile flag is necessary to run checks like the compile-time assertions on size and alignment calculations.
verus lib.rs --compile --expand-errors -L dependency=../../deps_hack/target/debug/deps --extern=deps_hack=../../deps_hack/target/debug/libdeps_hack.rlib $@ 