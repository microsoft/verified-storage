#!/bin/bash

PM_DEVICE=$1
MOUNT_POINT=$2
result_dir=$3

if [ -z "$PM_DEVICE" ]
then 
    echo "Please provide a PM device to use (e.g., /dev/pmem0)"
    exit 1
fi

if [ -z "$MOUNT_POINT" ]
then 
    echo "Please provide a mount point (e.g., /mnt/pmem"
    exit 1
fi


if [ -z "$result_dir" ]
then 
    echo "Please provide a directory to store output in"
    exit 1
fi

mkdir -p $result_dir
cd verif-storage-eval
iterations=9 # 10 total, 0-9

append_size=128
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=256
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=512
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=1024
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=4096
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=8192
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=65536
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=131072
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=262144
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval $PM_DEVICE $MOUNT_POINT $append_size >> ../$result_dir/results_$append_size.csv
done

