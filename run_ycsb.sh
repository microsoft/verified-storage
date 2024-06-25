#!/bin/bash

DB=$1
export LD_LIBRARY_PATH=~/verified-storage/ycsb_ffi/target/debug

set -e

cd ycsb_ffi
cargo run 

cd ../YCSB
./bin/ycsb load $DB -s -P workloads/workloada
./bin/ycsb run $DB -s -P workloads/workloada