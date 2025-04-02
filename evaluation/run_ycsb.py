#!/bin/python3 

import argparse
import toml
import subprocess
import os
import time
import sys
from pathlib import Path

DBS = ["capybarakv", "pmemrocksdb", "redis", "viper"]

def is_windows():
    return sys.platform.startswith("win")

def main():
    # Get command line arguments
    parser = arg_parser()
    args = parser.parse_args()
    db = args.db
    experiment_config_file = args.experiment_config
    capybarakv_config_file = args.capybarakv_config

    configs = {}

    # Read the experiment config file to get other configurable info
    with open(experiment_config_file) as f:
        contents = f.read()
        configs = toml.loads(contents)
    configs = configs["experiment_config"]

    output_dir_paths = create_output_dirs(configs, db)

    if not db in DBS: 
        print("Unknown db", db)
        return -1

    print("Running workloads", args.workloads)

    run_experiment(configs, db, output_dir_paths, args.workloads, experiment_config_file, capybarakv_config_file)

def list_of_strings(arg):
    return [s.upper() for s in arg.split(',')]

def arg_parser():
    # Most arguments are obtained from the config file, not command line.
    parser = argparse.ArgumentParser()
    parser.add_argument("--db", type=str, help="select database to run workloads on", required=True)
    parser.add_argument("--workloads", 
        type=list_of_strings, 
        help="select workloads to run as a comma separated list. \
            Options are A, B, C, D, E, F, X, Y, Z. The script will \
            automatically run required load operations for the \
            selected workloads. All workloads are run if this \
            argument is not provided.", 
        required=False,
        default=["A", "B", "C", "D", "E", "F", "X", "Y", "Z"])
    parser.add_argument("--experiment_config", type=str, 
        help="path to the experiment config file to use", default="experiment_config.toml")
    parser.add_argument("--capybarakv_config", type=str, 
        help="path to the capybarakv config file to use", default="capybarakv_config.toml")

    return parser

def setup_pm(configs):
    if is_windows():
        return

    pm_device = configs["pm_device"]
    mount_point = configs["mount_point"]

    subprocess.call(["sudo", "umount", pm_device]); # this may fail if FS is not mounted, but this is fine
    subprocess.check_call(["sudo", "mkfs.ext4", pm_device, "-F"]);
    subprocess.check_call(["sudo", "mount", "-o", "dax", pm_device, mount_point]);
    subprocess.check_call(["sudo", "chmod", "777", mount_point])

def remount_pm(configs):
    pm_device = configs["pm_device"]
    mount_point = configs["mount_point"]

    subprocess.check_call(["sudo", "umount", pm_device]);
    subprocess.check_call(["sudo", "mount", "-o", "dax", pm_device, mount_point]);

def setup_capybarakv(configs, experiment_config_file, capybarakv_config_file):
    if is_windows():
        import glob

        # Get the directory from the config
        kv_dir = os.path.dirname(configs["mount_point"])
        # Delete any existing capybarakv files
        for f in glob.glob(os.path.join(kv_dir, "capybarakv*")):
            try:
                os.remove(f)
            except OSError as e:
                print(f"Error deleting {f}: {e}")

        subprocess_under_dir(
            "ycsb_ffi",
            ["ycsb_ffi.exe", f"{os.path.join('..', capybarakv_config_file)}", f"{os.path.join('..', experiment_config_file)}"],
            stdout=subprocess.PIPE
        )

    else:
        subprocess.check_call(
            ["cargo", "run", "--release", "--", os.path.join("..", capybarakv_config_file), os.path.join("..", experiment_config_file)], 
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
    if is_windows():
        return

    if db == "redis":
        print("terminating redis process")
        subprocess.call(["sudo", "pkill", "redis"])
    time.sleep(5)
    subprocess.call(["sudo", "umount", configs["pm_device"]]);

def create_output_dirs(configs, db):
    results_dir = configs["results_dir"]
    # On Windows, mode parameter is ignored for os.makedirs
    mode = 0o777 if not is_windows() else None

    paths = [
        Path(results_dir, db, "Loada"),
        Path(results_dir, db, "Runa"),
        Path(results_dir, db, "Runb"),
        Path(results_dir, db, "Runc"),
        Path(results_dir, db, "Rund"),
        Path(results_dir, db, "Loade"),
        Path(results_dir, db, "Runf"),
        Path(results_dir, db, "Loadx"),
        Path(results_dir, db, "Runx"),
        Path(results_dir, db, "Loady"),
        Path(results_dir, db, "Runy"),
        Path(results_dir, db, "Loadz"),
        Path(results_dir, db, "Runz")
    ]

    for path in paths:
        if mode is None:
            os.makedirs(path, exist_ok=True)
        else:
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

def run_load_y_check(workloads):
    if "Y" in workloads:
        return True
    return False

def run_load_z_check(workloads):
    if "Z" in workloads:
        return True
    return False

def subprocess_under_dir(dir, cmd, stdout, stderr=None, check=True):
    original_cwd = os.getcwd()
    try:
        os.chdir(dir)
        print(f"Running command: {' '.join(cmd)} in {dir}")
        if stderr != None:
            return subprocess.run(cmd, stdout=stdout, stderr=stderr, check=check)
        else:
            return subprocess.run(cmd, stdout=stdout, check=check)
    finally:
        os.chdir(original_cwd)

def get_ycsb_path():
    if is_windows():
        return ".\\bin\\ycsb.bat"
    else:
        return "./bin/ycsb"
    
def run_experiment(configs, db, output_dir_paths, workloads, experiment_config_file, capybarakv_config_file):
    iterations = configs["iterations"]
    p = None

    options = build_options(configs, db, experiment_config_file, capybarakv_config_file)

    for i in range(1, iterations+1):
        loada_output_path = os.path.join(output_dir_paths[0], "Run" + str(i))
        runa_output_path = os.path.join(output_dir_paths[1], "Run" + str(i))
        runb_output_path = os.path.join(output_dir_paths[2], "Run" + str(i))
        runc_output_path = os.path.join(output_dir_paths[3], "Run" + str(i))
        rund_output_path = os.path.join(output_dir_paths[4], "Run" + str(i))
        loade_output_path = os.path.join(output_dir_paths[5], "Run" + str(i))
        runf_output_path = os.path.join(output_dir_paths[6], "Run" + str(i))
        loadx_output_path = os.path.join(output_dir_paths[7], "Run" + str(i))
        runx_output_path = os.path.join(output_dir_paths[8], "Run" + str(i))
        loady_output_path = os.path.join(output_dir_paths[9], "Run" + str(i))
        runy_output_path = os.path.join(output_dir_paths[10], "Run" + str(i))
        loadz_output_path = os.path.join(output_dir_paths[11], "Run" + str(i))
        runz_output_path = os.path.join(output_dir_paths[12], "Run" + str(i))

        # make sure viper is built correctly for non-x workloads. 
        # if we're only running workload x this will do some unnecessary work
        # but it's quick so it doesn't really matter
        rebuild_viper_wrapper(False)

        if run_load_a_check(workloads):
            setup_pm(configs)

            with open(loada_output_path, "w") as f:
                p = subprocess.Popen("df", stdout=subprocess.PIPE)
                output = p.communicate()[0]
                for line in str(output).split("\\n"):                 
                    if configs["mount_point"] in line:
                        f.write("Pre-experiment storage stats: ")
                        f.write(line)
                        f.write("\n")
                        break

            if db == "capybarakv":
                setup_capybarakv(configs, experiment_config_file, capybarakv_config_file)
            if db == "redis":
                p = setup_redis(configs)
        
            with open(loada_output_path, "a") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "load", db, "-s", "-P", "workloads/workloada"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
                p = subprocess.Popen("df", stdout=subprocess.PIPE)
                output = p.communicate()[0]
                for line in str(output).split("\\n"):                 
                    if configs["mount_point"] in line:
                        f.write("Post-experiment storage stats: ")
                        f.write(line)
                        f.write("\n")
                        break
                

            if "A" in workloads:
                with open(runa_output_path, "w") as f:
                    subprocess_under_dir("YCSB/",
                        [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloada"] + options, 
                        stdout=f,
                        # stderr=f,
                        check=True)

            if "B" in workloads:
                with open(runb_output_path, "w") as f:
                    subprocess_under_dir("YCSB/",
                        [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadb"] + options, 
                        stdout=f,
                        # stderr=f,
                        check=True)

            if "C" in workloads:
                with open(runc_output_path, "w") as f:
                    subprocess_under_dir("YCSB/",
                        [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadc"] + options, 
                        stdout=f,
                        # stderr=f,
                        check=True)
        
            if "D" in workloads:
                with open(rund_output_path, "w") as f:
                    subprocess_under_dir("YCSB/",
                        [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadd"] + options, 
                        stdout=f,
                        # stderr=f,
                        check=True)

        if run_load_e_check(workloads):
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs, experiment_config_file, capybarakv_config_file)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            else:
                setup_pm(configs)

            with open(loade_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "load", db, "-s", "-P", "workloads/workloade"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
            if "F" in workloads:
                with open(runf_output_path, "w") as f:
                    subprocess_under_dir("YCSB/",
                        [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadf"] + options, 
                        stdout=f,
                        # stderr=f,
                        check=True)

        if run_load_x_check(workloads):
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs, experiment_config_file, capybarakv_config_file)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            elif db == "viper":
                # we need to rebuild the viper wrapper to use the correct 
                # key size for workload x
                rebuild_viper_wrapper(True)
                options += ["-p", "viper.value_size=1024"]
                setup_pm(configs)
            else:
                setup_pm(configs)

            with open(loadx_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "load", db, "-s", "-P", "workloads/workloadx"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
            with open(runx_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadx"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
        
        if run_load_y_check(workloads):
            # we only run this with capybarakv, but the others can support it too
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs, experiment_config_file, capybarakv_config_file)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            else:
                setup_pm(configs)

            with open(loady_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "load", db, "-s", "-P", "workloads/workloady"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
            with open(runy_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloady"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)

        if run_load_z_check(workloads):
            # we only run this with capybarakv, but the others can support it too
            if db == "capybarakv":
                setup_pm(configs)
                setup_capybarakv(configs, experiment_config_file, capybarakv_config_file)
            elif db == "redis":
                cleanup(configs, db, redis_process=p)
                setup_pm(configs)
                p = setup_redis(configs)
            else:
                setup_pm(configs)

            with open(loadz_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "load", db, "-s", "-P", "workloads/workloadz"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
            with open(runz_output_path, "w") as f:
                subprocess_under_dir("YCSB/",
                    [get_ycsb_path(), "run", db, "-s", "-P", "workloads/workloadz"] + options, 
                    stdout=f,
                    # stderr=f,
                    check=True)
                
        if db == "redis":
            cleanup(configs, db, redis_process=p)
        if db == "viper":
            # rebuild so that it works for other workloads in the future
            rebuild_viper_wrapper(False)

def rebuild_viper_wrapper(x):
    subprocess.check_call(["make", "clean"], cwd="viper_wrapper/")
    if x:
        subprocess.check_call(["make", "shared_x"], cwd="viper_wrapper/")
    else:
        subprocess.check_call(["make", "shared"], cwd="viper_wrapper/")

def build_options(configs, db, experiment_config_file, capybarakv_config_file):
    iterations = configs["iterations"]
    threads = configs["threads"]
    mount_point = configs["mount_point"]
    op_count = configs["op_count"]
    record_count = configs["record_count"]
    results_dir = configs["results_dir"]
    viper_initial_size = configs["viper_initial_size"]

    # TODO: get DB-specific options from config files rather than hardcoding them?

    # build options string, including DB-specific options
    options = []
    options += ["-p", "recordcount=" + str(record_count)]
    options += ["-p", "operationcount=" + str(op_count)]
    options += ["-threads", str(threads)]
    # options += ["-p", "measurementtype=histogram"]
    # options += ["-p", "hdrhistogram.fileoutput=true"]

    if db == "capybarakv":
        options += ["-p", "capybarakv.configfile=" + os.path.join("..", capybarakv_config_file)]
        options += ["-p", "experiment.configfile=" + os.path.join("..", experiment_config_file)]

    elif db == "redis":
        options += ["-p", "redis.host=127.0.0.1"]
        options += ["-p", "redis.port=6379"]
    elif db == "pmemrocksdb":
        options += ["-p", "rocksdb.dir=" + mount_point]
        # the rest of these options are hardcoded in the YCSB client
        # options += ["-p", "rocksdb.allow_mmap_reads=true"]
        # options += ["-p", "rocksdb.allow_mmap_writes=true"]
        # options += ["-p", "max_background_compaction=4"]
    elif db == "viper":
        options += ["-p", "viper.initialpoolsize=" + str(viper_initial_size)]
    elif db != "viper": # viper currently has no specific arguments
        assert False, "Not implemented"
    
    return options
    
main()