#!/bin/bash

DB=$1
RESULTS_DIR=$2
PM=$3
OP_COUNT=500000
RECORD_COUNT=500000
mount_point=/mnt/pmem
pm_device=/dev/pmem0
dram_db_dir=/home/hayley/kv_files

REDIS_PID=0

setup_capybarakv() {
    use_pm=$1
    target_dir=""
    echo "Setting up CapybaraKV"
    if [ $use_pm = true ]; then 
        setup_pm
        target_dir=$mount_point
    else 
        rm -rf $dram_db_dir 2> /dev/null
        mkdir -p $dram_db_dir
        check_error $?
        target_dir=$dram_db_dir
    fi
    # cd ../ycsb_ffi # todo: move this functionality to the other crate
    # cargo run
    # check_error $?
    # cd ../YCSB
}

setup_redis() {
    
    use_pm=$1
    # kill existing redis process, if any
    if [ $REDIS_PID != 0 ]; then 
        echo "Killing redis server with PID $REDIS_PID"
        kill $REDIS_PID
        sleep 1
    fi 
    if [ $use_pm = true ]; then 
        setup_pm
        cd ../pmem-redis 
        ./src/redis-server --nvm-maxcapacity 1 --nvm-dir $mount_point --nvm-threshold 0 &
        REDIS_PID=$!
        echo "redis is running with PID $REDIS_PID"
        cd ../YCSB
    else 
        rm -rf $dram_db_dir 2> /dev/null
        mkdir -p $dram_db_dir
        cd redis 
        ./src/redis-server --dir $dram_db_dir &
        REDIS_PID=$!
        cd ..
    fi
}

setup_pm() {
    echo "Creating new EXT4-DAX file system on device $pm_device at mount point $mount_point"
    sudo umount $pm_device 
    sudo mkfs.ext4 $pm_device -F
    check_error $?
    sudo mount -o dax $pm_device $mount_point
    check_error $?
    sudo chmod 777 $mount_point
    echo "Mounted EXT4-DAX"
}

cleanup() {
    if [ $REDIS_PID != 0 ]; then 
        echo "Killing redis server with PID $REDIS_PID"
        kill $REDIS_PID
        sleep 1
    fi 
    sudo umount $pm_device
}

check_error() {
    if [ $1 != 0 ]; then 
        echo "Error $1, exiting"
        exit $1
    fi
}

use_pm=false
if [ ! -z $PM ] && [ $PM = "--pm" ]; then 
    use_pm=true
    echo "Using persistent memory"
fi

options=""
if [ $DB = "rocksdb" ]; then 
    options="-p rocksdb.dir=~/rocksdb_files -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true"
elif [ $DB = "redis" ]; then 
    options="-p redis.host=127.0.0.1 -p redis.port=6379"
elif [ $DB = "capybarakv" ]; then 
    options="-p capybarakv.config=../capybarak_interface/config.toml"
fi 

cd YCSB
if [ $DB = "capybarakv" ]; then 
    setup_capybarakv $use_pm
elif [ $DB = "redis" ]; then 
    echo "Starting redis..."
    setup_redis $use_pm
fi

cd .. 
mkdir -p $RESULTS_DIR

# magic-trace run -multi-thread ./bin/ycsb -- load $DB -threads 1 -s -P workloads/workloada -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options
cd capybarakv_interface 
cargo build
magic-trace run -o ../$RESULTS_DIR/trace.fxt -trigger capybarakv_stop_indicator target/debug/capybarakv_interface -- --nocapture #&
# PID=$!
# echo "capybarakv PID: $PID"
# magic-trace attach -o ../$RESULTS_DIR/trace.fxt -pid $PID -trigger capybarakv_interface::capybarakv_stop_indicator
# cargo test loada_test -- --nocapture

# wait for the capybarakv process to complete
# while kill -0 $PID 2> /dev/null; do 
#     sleep 1
# done 
echo "Done, cleaning up"
cleanup



# magic-trace run -timer-resolution high java -- -cp /mnt/local_ssd/home/hayley/verified-storage/evaluation/YCSB/capybarakv/conf:/mnt/local_ssd/home/hayley/verified-storage/evaluation/YCSB/capybarakv/target/capybarakv-binding-0.18.0-SNAPSHOT.jar:/home/hayley/.m2/repository/org/apache/htrace/htrace-core4/4.1.0-incubating/htrace-core4-4.1.0-incubating.jar:/home/hayley/.m2/repository/org/slf4j/slf4j-api/1.7.25/slf4j-api-1.7.25.jar:/home/hayley/.m2/repository/org/hdrhistogram/HdrHistogram/2.1.4/HdrHistogram-2.1.4.jar:/home/hayley/.m2/repository/org/codehaus/jackson/jackson-mapper-asl/1.9.4/jackson-mapper-asl-1.9.4.jar:/home/hayley/.m2/repository/org/codehaus/jackson/jackson-core-asl/1.9.4/jackson-core-asl-1.9.4.jar:/mnt/local_ssd/home/hayley/verified-storage/evaluation/YCSB/core/target/core-0.18.0-SNAPSHOT.jar site.ycsb.Client -db site.ycsb.db.CapybaraKVClient -threads 1 -s -P workloads/workloada -p recordcount=500000 -p operationcount=500000 -p capybarakv.config=../ycsb_ffi/config.toml -load