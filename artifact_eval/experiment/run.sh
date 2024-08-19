#!/bin/bash

result_dir=$1

if [ -z "$result_dir" ]
then 
    echo "please provide an output directory"
    exit 1
fi

mkdir -p $result_dir
cd verif-storage-eval
cargo build --release
iterations=9

append_size=128
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=256
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=512
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=1024
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=4096
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=8192
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=65536
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=131072
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

append_size=262144
echo $append_size
for i in $(seq 0 $iterations)
do
    echo "iter $i"
    sudo ./target/release/verif-storage-eval /dev/pmem1 /mnt/pmem1 $append_size >> ../$result_dir/results_$append_size.csv
done

