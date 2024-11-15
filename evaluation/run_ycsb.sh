#!/bin/bash

DB=$1
RESULTS_DIR=$2
PM=$3
OP_COUNT=5000000
RECORD_COUNT=5000000
# OP_COUNT=500000
# RECORD_COUNT=500000
mount_point=/mnt/pmem
pm_device=/dev/pmem0
dram_db_dir=~/db_files # TODO: should this be in /tmp?
iterations=10

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
        mkdir $dram_db_dir
        check_error $?
        target_dir=$dram_db_dir
    fi
    cd ../ycsb_ffi
    pwd
    cargo run -- ../capybarakv_config.toml
    check_error $?
    cd ../YCSB
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
        mkdir $dram_db_dir
        cd redis 
        ./src/redis-server --dir $dram_db_dir &
        REDIS_PID=$!
        cd ..
    fi
}

setup_rocksdb() {
    use_pm=$1
    if [ $use_pm = true ]; then 
        setup_pm
    else 
        rm -rf $dram_db_dir 2> /dev/null
        mkdir $dram_db_dir
        check_error $?
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

# TODO: may need to be sure to source .bashrc?

use_pm=false
if [ $PM == "--pm" ]; then 
    use_pm=true
    echo "Using persistent memory"
fi

options=""
if [ $DB = "rocksdb" ]; then 
    if [ $PM == "--pm" ]; then
        DB="pmemrocksdb"
        options="-p rocksdb.dir=$mount_point -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true"
    else 
        options="-p rocksdb.dir=$dram_db_dir -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true"
    fi
elif [ $DB = "pmemrocksdb" ]; then 
    options="-p rocksdb.dir=$mount_point -p rocksdb.allow_mmap_reads=true -p rocksdb.allow_mmap_writes=true"
elif [ $DB = "redis" ]; then 
    options="-p redis.host=127.0.0.1 -p redis.port=6379"
elif [ $DB = "capybarakv" ]; then 
    options="-p capybarakv.configfile=../capybarakv_config.toml"
fi 

echo $options

export LD_LIBRARY_PATH=~/verified-storage/evaluation/ycsb_ffi/target/debug



mkdir -p $RESULTS_DIR/$DB/Loada
check_error $?
mkdir -p $RESULTS_DIR/$DB/Runa
check_error $?
mkdir -p $RESULTS_DIR/$DB/Runb
check_error $?
mkdir -p $RESULTS_DIR/$DB/Runc
check_error $?
mkdir -p $RESULTS_DIR/$DB/Loade
check_error $?
mkdir -p $RESULTS_DIR/$DB/Runf
check_error $?
sudo chmod 777 $RESULTS_DIR -R

cd YCSB

for iter in $(seq $iterations); do 
    if [ $DB = "capybarakv" ]; then 
        setup_capybarakv $use_pm
    elif [ $DB = "redis" ]; then 
        echo "Starting redis..."
        setup_redis $use_pm
    elif [ $DB = "rocksdb" ] || [ $DB = "pmemrocksdb" ]; then 
        setup_rocksdb $use_pm
    else 
        echo "Unrecognized database $DB"
        exit 1
    fi

    ./bin/ycsb load $DB -threads 1 -s -P workloads/workloada -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Loada/Run$iter
    check_error $?
    ./bin/ycsb run $DB -threads 1 -s -P workloads/workloada -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Runa/Run$iter
    check_error $?
    ./bin/ycsb run $DB -threads 1 -s -P workloads/workloadb -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Runb/Run$iter
    check_error $?
    ./bin/ycsb run $DB -threads 1 -s -P workloads/workloadc -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Runc/Run$iter
    check_error $?

    if [ $DB = "capybarakv" ]; then 
        setup_capybarakv $use_pm
    elif [ $DB = "redis" ]; then 
        setup_redis $use_pm
    elif [ $DB = "rocksdb" ] || [ $DB = "pmemrocksdb" ]; then 
        setup_rocksdb $use_pm
    else 
        echo "Unrecognized database $DB"
        exit 1
    fi
    ./bin/ycsb load $DB -threads 1 -s -P workloads/workloade -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Loade/Run$iter
    check_error $?
    ./bin/ycsb run $DB -threads 1 -s -P workloads/workloadf -p recordcount=$RECORD_COUNT -p operationcount=$OP_COUNT $options > ../$RESULTS_DIR/$DB/Runf/Run$iter
    check_error $?

    cleanup
done