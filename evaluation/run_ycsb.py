#!/bin/python3 

import argparse
import toml
import subprocess
import os
import time
import sys
from pathlib import Path

DBS = ["capybarakv", "pmemrocksdb", "redis"]

def main():
    # Get command line arguments
    parser = arg_parser()
    args = parser.parse_args()
    db = args.db

    configs = {}

    # Read the experiment config file to get other configurable info
    with open("experiment_config.toml") as f:
        contents = f.read()
        configs = toml.loads(contents)
    configs = configs["experiment_config"]

    output_dir_paths = create_output_dirs(configs, db)

    if not db in DBS: 
        print("Unknown db", db)
        return -1

    print("Running workloads", args.workloads)

    run_experiment(configs, db, output_dir_paths, args.workloads)

def list_of_strings(arg):
    return [s.upper() for s in arg.split(',')]

def arg_parser():
    # Most arguments are obtained from the config file, not command line.
    parser = argparse.ArgumentParser()
    parser.add_argument("--db", type=str, help="select database to run workloads on", required=True)
    parser.add_argument("--workloads", 
        type=list_of_strings, 
        help="select workloads to run as a comma separated list. \
            Options are A, B, C, D, E, F, and X. The script will \
            automatically run required load operations for the \
            selected workloads. All workloads are run if this \
            argument is not provided.", 
        required=False,
        default=["A", "B", "C", "D", "E", "F", "X"])

    return parser

def setup_pm(configs):
    pm_device = configs["pm_device"]
    mount_point = configs["mount_point"]

    subprocess.call(["sudo", "umount", pm_device]); # this may fail if FS is not mounted, but this is fine
    subprocess.check_call(["sudo", "mkfs.ext4", pm_device, "-F"]);
    subprocess.check_call(["sudo", "mount", "-o", "dax", pm_device, mount_point]);
    subprocess.check_call(["sudo", "chmod", "777", mount_point])

def setup_capybarakv(configs):
    subprocess.check_call(
        ["cargo", "run", "--release", "--", "../capybarakv_config.toml", "../experiment_config.toml"], 
        cwd="ycsb_ffi/"
    )

def setup_redis(configs):
    # start the redis server in the background
    p = subprocess.Popen(
        ["sudo", "./src/redis-server", "redis.conf"],
        cwd="pmem-redis/"
    )
    return p

def cleanup(configs, db, redis_process=None):
    if db == "redis":
        print("terminating redis process")
        subprocess.call(["sudo", "pkill", "redis"])
    time.sleep(5)
    subprocess.call(["sudo", "umount", configs["pm_device"]]);

def create_output_dirs(configs, db):
    results_dir = configs["results_dir"]
    mode = 0o777

    paths = [
        Path(results_dir, db, "Loada"),
        Path(results_dir, db, "Runa"),
        Path(results_dir, db, "Runb"),
        Path(results_dir, db, "Runc"),
        Path(results_dir, db, "Loade"),
        Path(results_dir, db, "Runf"),
        Path(results_dir, db, "Loadx"),
        Path(results_dir, db, "Runx")
    ]

    for path in paths:
        os.makedirs(path, mode, exist_ok=True)
    return paths

def run_load_a_check(workloads):
    for w in ["A", "B", "C", "D"]:
        if w in workloads:
            return True 
    return False

def run_load_e_check(workloads):
    for w in ["E", "F"]:
        if w in workloads:
            return True 
    return False

def run_load_x_check(workloads):
    if "X" in workloads:
        return True 
    return False
    
def run_experiment(configs, db, output_dir_paths, workloads):
    iterations = configs["iterations"]
    p = None

    options = build_options(configs, db)

    for i in range(1, iterations+1):
        loada_output_path = os.path.join(output_dir_paths[0], "Run" + str(i))
        runa_output_path = os.path.join(output_dir_paths[1], "Run" + str(i))
        runb_output_path = os.path.join(output_dir_paths[2], "Run" + str(i))
        runc_output_path = os.path.join(output_dir_paths[3], "Run" + str(i))
        loade_output_path = os.path.join(output_dir_paths[4], "Run" + str(i))
        runf_output_path = os.path.join(output_dir_paths[5], "Run" + str(i))
        loadx_output_path = os.path.join(output_dir_paths[6], "Run" + str(i))
        runx_output_path = os.path.join(output_dir_paths[7], "Run" + str(i))

        if run_load_a_check(workloads):
            setup_pm(configs)
            if db == "capybarakv":
                setup_capybarakv(configs)
            if db == "redis":
                p = setup_redis(configs)
        
            with open(loada_output_path, "w") as f:
                subprocess.run(
                    ["./bin/ycsb", "--", "load", db, "-s", "-P", "workloads/workloada"] + options, 
                    cwd="YCSB/",
                    stdout=f,
                    # stderr=f,
                    check=True)

            if "A" in workloads:
                with open(runa_output_path, "w") as f:
                    subprocess.run(
                        ["./bin/ycsb", "--", "run", db, "-s", "-P", "workloads/workloada"] + options, 
                        cwd="YCSB/",
                        stdout=f,
                        # stderr=f,
                        check=True)
            if "B" in workloads:
                with open(runb_output_path, "w") as f:
                    subprocess.run(
                        ["./bin/ycsb", "--", "run", db, "-s", "-P", "workloads/workloadb"] + options, 
                        cwd="YCSB/",
                        stdout=f,
                        # stderr=f,
                        check=True)
            if "C" in workloads:
                with open(runc_output_path, "w") as f:
                    subprocess.run(
                        ["./bin/ycsb", "--", "run", db, "-s", "-P", "workloads/workloadc"] + options, 
                        cwd="YCSB/",
                        stdout=f,
                        # stderr=f,
                        check=True)

        if run_load_e_check(workloads):
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            else:
                setup_pm(configs)

            with open(loade_output_path, "w") as f:
                subprocess.run(
                    ["./bin/ycsb", "--", "load", db, "-s", "-P", "workloads/workloade"] + options, 
                    cwd="YCSB/",
                    stdout=f,
                    # stderr=f,
                    check=True)
            if "F" in workloads:
                with open(runf_output_path, "w") as f:
                    subprocess.run(
                        ["./bin/ycsb", "--", "run", db, "-s", "-P", "workloads/workloadf"] + options, 
                        cwd="YCSB/",
                        stdout=f,
                        # stderr=f,
                        check=True)

        if run_load_x_check(workloads):
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            else:
                setup_pm(configs)

            with open(loadx_output_path, "w") as f:
                subprocess.run(
                    ["./bin/ycsb", "--", "load", db, "-s", "-P", "workloads/workloadx"] + options, 
                    cwd="YCSB/",
                    stdout=f,
                    # stderr=f,
                    check=True)
            with open(runx_output_path, "w") as f:
                subprocess.run(
                    ["./bin/ycsb", "--", "run", db, "-s", "-P", "workloads/workloadx"] + options, 
                    cwd="YCSB/",
                    stdout=f,
                    # stderr=f,
                    check=True)
                
        if db == "redis":
            cleanup(configs, db, redis_process=p)

def build_options(configs, db):
    iterations = configs["iterations"]
    threads = configs["threads"]
    mount_point = configs["mount_point"]
    op_count = configs["op_count"]
    record_count = configs["record_count"]
    results_dir = configs["results_dir"]

    # TODO: get DB-specific options from config files rather than hardcoding them?

    # build options string, including DB-specific options
    options = []
    options += ["-p", "recordcount=" + str(record_count)]
    options += ["-p", "operationcount=" + str(op_count)]
    options += ["-threads", str(threads)]

    if db == "capybarakv":
        options += ["-p", "capybarakv.configfile=../capybarakv_config.toml"]
        options += ["-p", "experiment.configfile=../experiment_config.toml"]
    elif db == "redis":
        options += ["-p", "redis.host=127.0.0.1"]
        options += ["-p", "redis.port=6379"]
    elif db == "pmemrocksdb":
        options += ["-p", "rocksdb.dir=" + mount_point]
        options += ["-p", "rocksdb.allow_mmap_reads=true"]
        options += ["-p", "rocksdb.allow_mmap_writes=true"]
        options += ["-p", "options.env = rocksdb::NewDCPMMEnv(rocksdb::DCPMMEnvOptions());"]
    else:
        assert False, "Not implemented"
    
    return options
    
main()