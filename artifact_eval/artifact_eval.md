## VM setup

### Option 1 (recommended): use provided VM

### Option 2: create a new VM

1. Run [`setup.sh`](http://setup.sh) to download an Ubuntu cloud image and set it up. This script sets the username and password for login to `ubuntu`.
2. Run [`boot.sh`](http://boot.sh) to boot the VM. This starts the VM with 16 cores and 16GB of memory
3. Open a separate terminal and SSH in: `ssh ubuntu@localhostubuntu@localhost -p 2222`
4. The default kernel does not support all of the options required to emulate PM, so we have to build a new one. In the VM:
    1. Run `sudo apt-get install build-essential libncurses-dev bison flex libssl-dev libelf-dev` to install dependencies for building the kernel
    2. Download a compatible kernel version: `wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.15.165.tar.xz`. This will take several minutes.
    3. Untar the kernel: `tar -xvf linux-5.15.165.tar.xz`
    4. `cd linux-5.15.165` and set up a config file: `make oldconfig` . If it prompts you to select any new configuration options, hit Enter to select the default value.
    5. Run `make menuconfig` and use the GUI to select the following options required for PM emulation. Make sure to hit `Save` after changing options.
        1. `Cryptographic API -> Certificates for signature checking -> Provide system-wide ring of trusted keys -> Additional X.509 keys for default system keyring`  (`CONFIG_SYSTEM_TRUSTED_KEYS`): Set to an empty string
        2. `Cryptographic API -> Certificates for signature checking -> Provide system-wide ring of blacklisted keys -> Provide system-wide ring of revocation certificates -> X.509 certificates to be preloaded into the system blacklist keyring`   (`CONFIG_SYSTEM_REVOCATION_KEYS`): Set to an empty string
        3. `Kernel hacking -> Compile-time checks and compiler options -> Compile the kernel with debug info -> Generate BTF type information` (`CONFIG_DEBUG_INFO_BTF`): N
        4. `Memory Management options -> Allow for memory hot-add` (`CONFIG_MEMORY_HOTPLUG`): Y
        5. `Memory Management options -> Allow for memory hot remove` (`CONFIG_MEMORY_HOTREMOVE`): Y
        6. `Memory Management options -> Device memory (pmem, HMM, etc...) hotplug support` (`CONFIG_ZONE_DEVICE`): Y
        7. `Device drivers -> NVDIMM (Non-Volatile Memory Device) Support` (`CONFIG_LIBNVDIMM`): Y
        8. `Device drivers -> NVDIMM (Non-Volatile Memory Device) Support -> BTT: Block Translation Table (atomic sector updates)` (`CONFIG_BTT`): Y
        9.  `Device drivers -> NVDIMM (Non-Volatile Memory Device) Support -> PFN Map persistent (device) memory` (`CONFIG_NVDIMM_PFN`): Y
        10. `Device drivers -> NVDIMM (Non-Volatile Memory Device) Support -> NVDIMM DAX: Raw access to persistent memory` (`CONFIG_NVDIMM_PFN`): Y
        11. `Device drivers -> NVDIMM (Non-Volatile Memory Device) Support -> PMEM: Persistent memory block device support` (`CONFIG_BLK_DEV_PMEM`): M
        12. `Device drivers -> DAX: direct access to differentiated memory` (`CONFIG_DAX`): Y
        13. `Processor type and features -> Support non-standard NVDIMMs and ADR protected memory` (`CONFIG_X86_PMEM_LEGACY`): Y
        14. `File systems -> File system based Direct Access (DAX) support` (`CONFIG_FS_DAX`): Y
    6. Run `make -j 16` to build the kernel. 
5. Modify the `/etc/default/grub` file to set `GRUB_CMDLINE_LINUX` to `GRUB_CMDLINE_LINUX="memmap=6G!4G"`
6. Run `sudo update-grub2`
7. Reboot the VM and SSH back in. When you log back in, `ls /dev | grep pmem` should output `/dev/pmem0`. This is the emulated PM device we will use for the experiment.