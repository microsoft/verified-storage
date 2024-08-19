## VM setup

1. Run [`setup.sh`](http://setup.sh) to download an Ubuntu cloud image and set it up. This script sets the username and password for login to `ubuntu`.
2. Run [`boot.sh`](http://boot.sh) to boot the VM. This starts the VM with 16 cores and 16GB of memory.
3. Open a separate terminal and SSH in: `ssh ubuntu@localhostubuntu@localhost -p 2222`
4. In the VM, run the following commands to install Rust and dependencies for the experiment and PM emulation. 
    ```
    sudo apt update
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh 
    sudo apt install -y linux-generic llvm-dev libclang-dev clang libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev build-essential
    ```
5. Edit `/etc/default/grub` and change the line containing `GRUB_CMDLINE_LINUX` to `GRUB_CMDLINE_LINUX="memmap=8G!4G"`. 
6. Run `sudo update-grub` and reboot the VM. 
7. Log back into the VM and run `ls /dev | grep pmem`. The output should be `pmem0` -- this is the emulated PM device we will use for experiments.

## Running experiments

1. Clone this repository on the VM.
2. `cd artifact_eval/experiment/verif-storage-eval` and run `cargo build --release` to build the experiment crate and its dependencies, including PMDK and verified logs.