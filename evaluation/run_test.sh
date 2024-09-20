#!/bin/bash

DB=$1

setup() {
    cd ../ycsb_ffi
    cargo run 
    cd ../YCSB
}

options=""
if [ $DB = "rocksdb" ]; then 
    options="-p rocksdb.dir=~/rocksdb_files -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true"
elif [ $DB = "redis" ]; then 
    options="-p redis.host=127.0.0.1 -p redis.port=6379"
fi 

echo $options

export LD_LIBRARY_PATH=~/verified-storage/evaluation/ycsb_ffi/target/debug

cd YCSB
setup
./bin/ycsb load $DB -threads 1 -P ../workloads/trace_workload1 -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options