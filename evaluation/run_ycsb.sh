#!/bin/bash

DB=$1
OP_COUNT=500000
RECORD_COUNT=500000
results_dir=ycsb_results

setup_capybarakv() {
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

set -e

iter=1

mkdir -p $results_dir/$DB/Loada
mkdir -p $results_dir/$DB/Runa
mkdir -p $results_dir/$DB/Runb
mkdir -p $results_dir/$DB/Runc
mkdir -p $results_dir/$DB/Loade
mkdir -p $results_dir/$DB/Runf

cd YCSB
setup_capybarakv
./bin/ycsb load $DB -threads 1 -s -P workloads/workloada -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Loada/Run$iter
./bin/ycsb run $DB -threads 1 -s -P workloads/workloada -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Runa/Run$iter
./bin/ycsb run $DB -threads 1 -s -P workloads/workloadb -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Runb/Run$iter
./bin/ycsb run $DB -threads 1 -s -P workloads/workloadc -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Runc/Run$iter
# ./bin/ycsb run $DB -s -P workloads/workloadd -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT > ../results/$DB\_rund
setup_capybarakv
./bin/ycsb load $DB -threads 1 -s -P workloads/workloade -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Loade/Run$iter
# ./bin/ycsb run $DB -s -P workloads/workloade -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT > ../results/$DB\_rune
./bin/ycsb run $DB -threads 1 -s -P workloads/workloadf -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$results_dir/$DB/Runf/Run$iter