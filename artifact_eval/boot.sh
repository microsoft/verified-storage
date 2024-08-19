#!/usr/bin/bash

img=ubuntu-22.04-server-cloudimg-amd64.img
user_data=user-data.img

qemu-system-x86_64 \
  -drive "file=${img},format=qcow2" \
  -drive "file=${user_data},format=raw" \
  -enable-kvm \
  -m 16G \
  -net nic \
  -net user,hostfwd=tcp::2222-:22 \
  -cpu host \
  -smp 16 \
  -nographic
;