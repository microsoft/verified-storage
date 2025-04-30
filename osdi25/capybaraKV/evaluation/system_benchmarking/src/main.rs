#![allow(non_snake_case)]

use crc64fast::Digest;
use std::time::Instant;
use std::process::Command;
use std::fs::OpenOptions;
use std::path::Path;
use memmap::MmapOptions;




const CRC_ITERS: u64 = 10000;
const MMAP_ITERS: u64 = 100;
const MOUNT_POINT: &str = "/mnt/pmem/";
const PM_DEV: &str = "/dev/pmem0";

fn main() {
    measure_crc();
    measure_mmap();
}

#[allow(dead_code)]
#[derive(Default)]
struct BigStruct {
    v0: u128,
    v1: u128,
    v2: u128,
    v3: u128,
    v4: u128,
    v5: u128,
    v6: u128,
    v7: u128
}

fn measure_crc() {
    let mut timing_8B = Vec::new();
    let mut timing_128B = Vec::new();

    for i in 0..CRC_ITERS {
        let t0 = Instant::now();
        let mut digest = Digest::new();
        digest.write(&i.to_ne_bytes());
        let t1 = t0.elapsed().as_nanos();
        timing_8B.push(t1);
    }

    for i in 0..CRC_ITERS {
        let v = BigStruct::default();
        let bytes = unsafe {
            let ptr = &v as *const BigStruct as *const u8;
            std::slice::from_raw_parts(ptr, core::mem::size_of::<BigStruct>())
        };
        let t0 = Instant::now();
        let mut digest = Digest::new();
        digest.write(bytes);
        let t1 = t0.elapsed().as_nanos();
        timing_128B.push(t1);
    }

    let mut sum = 0;
    for i in 0..timing_8B.len() {
        sum += timing_8B[i];
    }
    println!("Average 8-byte CRC time: {:?} nsec", sum / timing_8B.len() as u128);

    let mut sum = 0;
    for i in 0..timing_128B.len() {
        sum += timing_128B[i];
    }
    println!("Average 128-byte CRC time: {:?} nsec", sum / timing_128B.len() as u128);
}

fn measure_mmap() {
    let mut mmap_1G_timing = Vec::new();
    let mut mmap_32G_timing = Vec::new();

    init_and_mount_pm_fs(MOUNT_POINT, PM_DEV);

    let file_size = 1024*1024*1024; // 1 GiB
    for i in 0..MMAP_ITERS {
        let path = Path::new(MOUNT_POINT).join(i.to_string());
        {
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .open(&path)
                .unwrap();
            file.set_len(file_size).unwrap();
            let t0 = Instant::now();
            let _mmap = unsafe { 
                MmapOptions::new()
                    .len(file_size.try_into().unwrap())
                    .map(&file)
                    .unwrap() 
                };
            let t1 = t0.elapsed().as_micros();
            mmap_1G_timing.push(t1);
        }
        init_and_mount_pm_fs(MOUNT_POINT, PM_DEV);
    }

    init_and_mount_pm_fs(MOUNT_POINT, PM_DEV);

    let file_size = 1024*1024*1024*32; // 32 GiB
    for i in 0..MMAP_ITERS {
        let path = Path::new(MOUNT_POINT).join(i.to_string());
        {
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .open(&path)
                .unwrap();
            file.set_len(file_size).unwrap();
            let t0 = Instant::now();
            let _mmap = unsafe { 
                MmapOptions::new()
                    .len(file_size.try_into().unwrap())
                    .map(&file)
                    .unwrap() 
                };
            let t1 = t0.elapsed().as_micros();
            mmap_32G_timing.push(t1);
        }
        init_and_mount_pm_fs(MOUNT_POINT, PM_DEV);
    }

    let mut sum = 0;
    for i in 0..mmap_1G_timing.len() {
        sum += mmap_1G_timing[i];
    }
    println!("Average 1GiB mmap time: {:?} usec", sum / mmap_1G_timing.len() as u128);

    let mut sum = 0;
    for i in 0..mmap_32G_timing.len() {
        sum += mmap_32G_timing[i];
    }
    println!("Average 32GiB mmap time: {:?} usec", sum / mmap_32G_timing.len() as u128);

    unmount_pm_fs(PM_DEV);
}

pub fn init_and_mount_pm_fs(mount_point: &str, pm_dev: &str) {
    unmount_pm_fs(pm_dev);

    // Set up PM with a fresh file system instance
    Command::new("sudo")
        .args(["mkfs.ext4", pm_dev, "-F"])
        .output()
        .expect("mkfs.ext4 failed");

    Command::new("sudo")
        .args(["mount", "-o", "dax", pm_dev, mount_point])
        .status()
        .expect("mount failed");

    Command::new("sudo")
        .args(["chmod", "777", mount_point])
        .status()
        .expect("chmod failed");
}


pub fn unmount_pm_fs(pm_dev: &str) {
    // sleep(Duration::from_secs(5));
    let _status = Command::new("sudo").args(["umount", pm_dev, "-f"]).output();
}