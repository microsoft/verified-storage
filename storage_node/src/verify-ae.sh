#!/bin/bash

OUTPUT_FILE="verif_output.txt"
RED="\e[31m"
GREEN="\e[32m"
MAGENTA="\e[35m"
BOLD=$(tput bold)
NC="\e[0m"

# clear
cd ../../deps_hack
echo "Building deps_hack"
cargo build
cd ../pmsafe
echo "Building pmsafe"
cargo build
cd ../storage_node/src
echo "Verifying"
# The --compile flag is necessary to run checks like the compile-time assertions on size and alignment calculations.
verus lib.rs --compile --expand-errors -L dependency=../../deps_hack/target/debug/deps --extern=deps_hack=../../deps_hack/target/debug/libdeps_hack.rlib $@ > $OUTPUT_FILE 2>&1



printf "\n\n${BOLD}${MAGENTA}Results:${NC}\n"
grep "verification results:" $OUTPUT_FILE
grep "total-time:" $OUTPUT_FILE

printf "\nVerification results written to ${OUTPUT_FILE}\n"