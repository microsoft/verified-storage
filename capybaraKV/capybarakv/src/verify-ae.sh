#!/bin/bash

timestamp=$(date +%s)
OUTPUT_FILE="verif_output_${timestamp}.txt"
RED="\e[31m"
GREEN="\e[32m"
MAGENTA="\e[35m"
BOLD=$(tput bold)
NC="\e[0m"

# # check that verus binary is on PATH and exit if not
# cmd=verus
# [[ $(type -P "$cmd") ]] && echo "$cmd is in PATH"  || 
#     { echo "$cmd is NOT in PATH" 1>&2; exit 1; }

# clear
cd ../../deps_hack
echo "Building deps_hack"
cargo build
cd ../pmcopy
echo "Building pmcopy"
cargo build
cd ../capybarakv/src
echo "Verifying"
echo "Arguments: $@" >> $OUTPUT_FILE
# The --compile flag is necessary to run checks like the compile-time assertions on size and alignment calculations.
../../../../../verus/source/target-verus/release/verus lib.rs --compile --expand-errors -L dependency=../../deps_hack/target/debug/deps --extern=deps_hack=../../deps_hack/target/debug/libdeps_hack.rlib $@ >> $OUTPUT_FILE 2>&1

printf "\n\n${BOLD}${MAGENTA}Results:${NC}\n"
grep "verification results:" $OUTPUT_FILE
grep "total-time:" $OUTPUT_FILE

printf "\nVerification results written to ${OUTPUT_FILE}\n"