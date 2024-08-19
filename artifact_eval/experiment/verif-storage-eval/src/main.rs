#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

extern crate sys_mount;

// TODO: make naming make more sense
use crate::log::LOG_SIZE;
use crate::multilog::VerifLog;
use crate::verif_log::OldVerifLog;
use log::PmemLog;
use pmdk_log::PmdkLog;
use std::time::Instant;
use std::{env, process::Command};
use sys_mount::{Mount, Unmount, UnmountDrop, UnmountFlags};

include!("./bindings.rs");

mod log;
mod multilog;
mod pmdk_log;
mod verif_log;

const BYTES_TO_APPEND: usize = 1024 * 1024 * 1024 * 8;

// automatically unmounts when dropped
fn mount(device: &str, mount_point: &str) -> UnmountDrop<Mount> {
    let _command = Command::new("mkfs.ext4").args([device]).output().unwrap();
    let mount = Mount::builder()
        .fstype("ext4")
        .data("dax")
        .mount(device, mount_point)
        .unwrap()
        .into_unmount_drop(UnmountFlags::DETACH);
    mount
}

fn run_pmdk_log(pm_device: String, mount_point: String, append_size: usize) {
    let _mount = mount(pm_device.as_str(), mount_point.as_str());
    let file_name = mount_point + "/pool";
    let mut pmdk_log: PmdkLog = PmdkLog::initialize(file_name, LOG_SIZE).unwrap();

    let mut bytes_appended = 0;
    let append_vec = vec![1; append_size];
    let now = Instant::now();
    while bytes_appended < BYTES_TO_APPEND {
        pmdk_log.append(&append_vec).unwrap();
        bytes_appended += append_size;
    }
    print!("{},", now.elapsed().as_micros());
}

fn run_verif_log(pm_device: String, mount_point: String, append_size: usize) {
    let _mount = mount(pm_device.as_str(), mount_point.as_str());
    let file_name = mount_point + "/pool";
    let mut verif_log: VerifLog = VerifLog::initialize(file_name, LOG_SIZE).unwrap();

    let mut bytes_appended = 0;
    let append_vec = vec![1; append_size];
    let now = Instant::now();
    while bytes_appended < BYTES_TO_APPEND {
        verif_log.append(&append_vec).unwrap();
        bytes_appended += append_size;
    }
    print!("{},", now.elapsed().as_micros());
}

fn run_old_verif_log(pm_device: String, mount_point: String, append_size: usize) {
    let _mount = mount(pm_device.as_str(), mount_point.as_str());
    let file_name = mount_point + "/pool";
    let mut verif_log: OldVerifLog = OldVerifLog::initialize(file_name, LOG_SIZE).unwrap();

    let mut bytes_appended = 0;
    let append_vec = vec![1; append_size];
    let now = Instant::now();
    while bytes_appended < BYTES_TO_APPEND {
        verif_log.append(&append_vec).unwrap();
        bytes_appended += append_size;
    }
    print!("{},", now.elapsed().as_micros());
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        println!("Usage: cargo run -- <device> <mount point> <append size>");
        return;
    }

    let pm_device = args[1].clone();
    let mount_point = args[2].clone();
    let append_size: usize = args[3].clone().parse().unwrap();
    let system = if args.len() == 5 {
        Some(args[4].clone())
    } else {
        None
    };

    // `pmdk` uses libpmemlog; `verif` uses the most up-to-date version of the verified log;
    // `old` uses the old version of the verified log with high serialization overhead
    if let Some(system) = system {
        if system == "pmdk" {
            print!("pmdk,");
            run_pmdk_log(pm_device.clone(), mount_point.clone(), append_size);
        } else if system == "verif" {
            print!("verif,");
            run_verif_log(pm_device, mount_point, append_size);
        } else if system == "old" {
            print!("old,");
            run_old_verif_log(pm_device, mount_point, append_size);
        }
    } else {
        // if neither log is specified, run both
        print!("pmdk,");
        run_pmdk_log(pm_device.clone(), mount_point.clone(), append_size);
        print!("\nverif,");
        run_verif_log(pm_device.clone(), mount_point.clone(), append_size);
        print!("\nold,");
        run_old_verif_log(pm_device, mount_point, append_size);
        println!("");
    }
}
