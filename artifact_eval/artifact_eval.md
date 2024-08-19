## VM setup

1. Run [`setup.sh`](http://setup.sh) to download an Ubuntu cloud image and set it up. This script sets the username and password for login to `ubuntu`.
2. Run [`boot.sh`](http://boot.sh) to boot the VM. This starts the VM with 16 cores and 16GB of memory.
3. Open a separate terminal and SSH in: `ssh ubuntu@localhostubuntu@localhost -p 2222`
4. In the VM, run the following commands to install dependencies for PM emulation and the persistent logs
    ```
    sudo apt install linux-generic llvm-dev libclang-dev clang libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev // installs PM dependencies
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh // installs Rust
    ```
5. Edit `/etc/default/grub` and change the line containing `GRUB_CMDLINE_LINUX` to `GRUB_CMDLINE_LINUX="memmap=8G!4G"`. 
6. Run `sudo update-grub` and reboot the VM. 
7. Log back into the VM and run `ls /dev | grep pmem`. The output should be `pmem0` -- this is the emulated PM device we will use for experiments.

## Running experiments
1. Clone this repository 