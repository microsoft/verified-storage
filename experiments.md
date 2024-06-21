# Experiments

## YCSB

### Setup
1. Install dependencies: `sudo apt install default-jdk default-jre maven`
2. Build the YCSB FFI layer: `cd ycsb_ffi; cargo build`.
2. Run `export LD_LIBRARY_PATH=~/verified-storage/ycsb_ffi/target/debug`
3. Run `cd YCSB; ./bin/ycsb load capybarakv -s -P workloads/workloada` to run workload Load A.