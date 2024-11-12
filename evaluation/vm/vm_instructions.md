# Testing VM instructions

## Initial setup
1. Run `./pm_vm_setup.sh`
2. Run `./pm_vm_boot.sh`. It will take a minute or so to boot.
3. In a separate terminal, run `ssh ubuntu@localhost -p 2222` to SSH into the VM. The password is `ubuntu`. 
4. In the SSH session, run the following commands to setup Rust and emulated PM:

```
sudo apt update
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain 1.79.0 -y
sudo apt install -y linux-generic llvm-dev libclang-dev clang libpmem1 libpmemlog1 libpmem-dev libpmemlog-dev build-essential python3-pip
pip3 install matplotlib scipy
sudo sed -i 's/GRUB_CMDLINE_LINUX=""/GRUB_CMDLINE_LINUX="memmap=8G!4G"/' /etc/default/grub
sudo update-grub
```

5. Reboot the VM (`sudo reboot -h now`)
6. Clone this repository on the VM.

You can now boot the VM using `./pm_vm_boot.sh` and log in via SSH.