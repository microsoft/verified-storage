## VM setup

1. Run [`setup.sh`](http://setup.sh) to download an Ubuntu cloud image and set it up. This script sets the username and password for login to `ubuntu`.
2. Run [`boot.sh`](http://boot.sh) to boot the VM. This starts the VM with 4 cores and 16GB of memory.
3. Open a separate terminal and SSH in: `ssh ubuntu@localhostubuntu@localhost -p 2222`
4. In the VM, run the following commands to install Rust and dependencies for the experiment and PM emulation. 
    ```
    sudo apt update
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh 
    sudo apt install -y linux-generic llvm-dev libclang-dev clang libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev build-essential python3-pip
    pip3 install matplotlib scipy
    ```
5. Edit `/etc/default/grub` and change the line containing `GRUB_CMDLINE_LINUX` to `GRUB_CMDLINE_LINUX="memmap=8G!4G"`. This will emulate 8GB of PM, starting at offset 4GB in DRAM.
6. Run `sudo update-grub` and reboot the VM. 
7. Log back into the VM and run `ls /dev | grep pmem`. The output should be `pmem0` -- this is the emulated PM device we will use for experiments.

## Running experiments

1. Clone this repository on the VM.
2. `cd artifact_eval/experiment/verif-storage-eval` and run `cargo build --release` to build the experiment crate and its dependencies, including PMDK and verified logs.
3. Run `sudo mkdir /mnt/pmem` to create a mount point for the experiment to use.
4. Move to the `artifact_eval/experiment` directory and run `run.sh /dev/pmem0 /mnt/pmem/ <output_dir>`.
    1. This command will run the full experiment (9 append sizes, 10 iterations each) on each of the three PM logs (the inital verified log, the current verified log, and PMDK's `libpmemlog`). The output will be placed in the directory indicated by the `output_dir` argument. 
    2. The experiment takes approximately 20-30 minutes to complete.

## Processing data

1. After running the experiment, run `python3 plot_verif_comparison.py <output_dir> 8192` in the `artifact_eval/experiment` directory on the VM.
    1. The 8192 argument is the total number of MB written to the log in each iteration. If you modify the `BYTES_TO_APPEND` value in `verif-storage-eval/src/main.rs`, this value should be set to the actual number of MB written.
2. The results will be plotted and saved in `artifact_eval/experiment/results.pdf`.

## Expected results

We expect the general pattern in the graph generated from these instructions to remain the same as that in the graph in the paper: PMDK and the latest verified version have similar throughput on all workloads, whereas the initial verified log has lower throughput due to its higher serialization overhead. However, we do expect some noticeable differences, as  the experimental data in the paper was obtained on Intel Optane PM and these instructions use emulated PM on regular DRAM. The results obtained by following these instructions are expected to differ from the paper results in the following ways.

1. The overall throughput for all three logs will be higher in the DRAM results. Optane PM has lower bandwidth and higher latency than DRAM. We obtain maximum throughput of approximately 13000 MiB/s for the PMDK and latest verified logs, and 10000 MiB/s on the initial verified log.
2. The initial verified log will have comparatively worse performance even as append sizes increase on DRAM. In the paper results, all three logs obtain similar performance on append sizes 64KiB and up, but we expect the initial log to consistently achieve lower throughput on all append sizes when run on DRAM. This is because the initial log has higher software overhead than the other two logs due to its non-optimal serialization approach that performs extra in-DRAM copying, which is dominated by the higher latency on Optane PM but has a bigger impact on performance when run on DRAM.
3. We expect larger error bars on the graph generated from these instructions than the one in the paper, as the results in the paper were obtained from experiments run on baremetal, whereas these instructions obtain results on VM.
4. On PM, the highest throughputs are obtained on append sizes of 4KiB and 8KiB, with larger append sizes plateauing a bit lower; on DRAM, we expect the highest throughputs to be obtained on append sizes 64KiB, 128KiB, and 256KiB. We attribute this to differences in maximum write bandwidth and to the larger variation of results obtained on VM. 