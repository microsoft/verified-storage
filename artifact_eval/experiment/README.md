# verif-storage-eval

## Overview

The `verif-storage-eval` crate compiles to a binary that can create and append to `libpmemlog` and verified `pmemlog` persistent logs. It uses [bindgen](https://rust-lang.github.io/rust-bindgen/) to automatically generate C-Rust bindings in order to call `libpmemlog` functions from Rust code.

The `PmemLog` trait defined in `log.rs` defines a common interface for both types of logs. `pmdk_log.rs` contains an implementation of the trait using `libpmemlog` and `verif_log.rs` contains an implementation using the verified log. 

`verif_log.rs` also contains an implementation of the `PersistentMemory` trait from the verified log that specifies how to read and write from the PM. We use PMDK's `pmem_memcpy_persist` function to perform all writes. This function writes data to PM (either using non-temporal stores or regular stores + cache line write backs) and issues a store fence before returning. 

When running a workload on one of the logs, the crate first mounts the Ext4-DAX file system and initializes the log, which creates the backing file and creates an empty log in it. The memory-mapped file is automatically closed when the log is freed, and the file system is automatically unmounted at the end of the experiment.

### Dependencies

Install the following packages before building the crate:
- `libpmem1`
- `libpmemlog1`
- `libpmem-dev`
- `libpmemlog-dev`

### Setup

1. Set the `pmemlog` dependency in Cargo.toml to either the verified-storage GitHub repository:
```
pmemlog = { git = "https://github.com/microsoft/verified-storage.git" }
```
OR to a local instance of the repo, e.g.:
```
pmemlog = { path = "/mnt/local_ssd/home/hayley/verified-storage/pmemlog" }
```

2. Set the total log size (`LOG_SIZE`) in `log.rs`. The crate will automatically create a file in the Ext4-DAX file system of this size and use it to back the logs. TODO: make this a command line argument

3. Set the total number of bytes to append in each experiment (`BYTES_TO_APPEND`) in `main.rs`. This number should be at least 128 bytes smaller (maybe more?) than `LOG_SIZE`, as both log implementations reserve some space for metadata. TODO: make this a command line argument

4. Check that PM is set up correctly. If using Intel Optane PM (real or emulated using `memmap` kernel command line argument), the PM should be in `fsdax` mode. See here https://docs.pmem.io/ndctl-user-guide/v/master/managing-nvdimms for more information on managing this type of PM.

5. Run `cargo build` to compile the crate and all dependencies.


### Running experiments

The method to run experiments differs slightly based on the permissions of the mount point.

If you need to use `sudo` to access the mount point, run experiments using:
```
sudo ./target/debug/verif-storage-eval <PM device> <mount point> <append size>
```
Otherwise, use 
```
cargo run -- <PM device> <mount point> <append size>
```
By default, the program will run the experiment with the specified append size on both logs. To only run it on one log, add `pmdk` or `verif` to the end of the command. 

The `run.sh` script runs 10 iterations of the experiment on several append sizes. To use it, just make sure the device size and mount point are set to the correct values for your setup.

### Output

Each experiment run produces output in the following form:
```
log,value
```
where `log` is the type of log (`pmdk` or `verif`) and `value` is the total time it took to append `BYTES_TO_APPEND` bytes to the log. This output can be redirected into a .csv file.

### Plotting results

The `plot_results.py` script produces a graph comparing the throughput of the two logs across different append sizes. The append sizes used are hardcoded in the script -- update the `append_sizes` list to change them. The script takes as arguments the name of a directory containing .csv files of results and the number of MB written in the experiment (so that it can correctly calculate throughput).
