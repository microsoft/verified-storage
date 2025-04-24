import sys
import os
from prettytable import PrettyTable

def parse_files(kvs, runs, result_dir):
    results = {kv: {"mem": [], "storage": []} for kv in kvs}

    for kv in kvs:
        for run in runs:
            filename = ""
            pre_blocks_used = 0
            post_blocks_used = 0
            # viper and capybarakv use special configs for these experiments, so the results are 
            # stored in a separate dir. redis and pmemrocksdb do not.
            if kv == "viper" or kv == "capybarakv":
                filename = os.path.join(result_dir, "mem_storage", kv, "Loada", "Run" + str(run))
            else:
                filename = os.path.join(result_dir, "threads_1", kv, "Loada", "Run" + str(run))
            in_file = open(filename, "r")
            lines = in_file.readlines()
            for line in lines:
                if "Mem usage" in line:
                    words = line.split()
                    # mem usage is recorded in bytes
                    perf = int(words[2]) / 1024**3
                    results[kv]["mem"].append(perf)

                # df output format is Filesystem, Size in 1K blocks, Used, Available, Use%, Mounted on
                # plus 3-word label at the beginning of the line 
                if "Pre-experiment storage stats" in line:
                    words = line.split()
                    pre_blocks_used = int(words[5])
                if "Post-experiment storage stats" in line:
                    words = line.split()
                    post_blocks_used = int(words[5])
            if pre_blocks_used == 0 or post_blocks_used == 0:
                print("Missing storage usage information")
                exit
            else:
                blocks_used = post_blocks_used - pre_blocks_used
                gb_used = blocks_used / 1024**2
                results[kv]["storage"].append(gb_used)
      
    final_results = {kv: {"mem": round(sum(results[kv]["mem"])/len(results[kv]["mem"]), 2),
                          "storage": round(sum(results[kv]["storage"])/len(results[kv]["storage"]), 2)} 
                        for kv in kvs}
    return final_results

def main():
    if len(sys.argv) < 5:
        print("Usage: python3 get_mem_and_storage_use.py <num_kvs> <kv1> <kv2> .. <num_runs> <start_run_id> <result_dir>")
        exit

    args = sys.argv[1:]

    num_kvs = int(args[0])
    kvs = []
    for i in range(0, num_kvs):
        kvs.append(args[i+1])

    num_runs = int(args[num_kvs+1])
    start_run_id = int(args[num_kvs+2])
    result_dir = args[num_kvs+3]

    runs = []
    for i in range(start_run_id, start_run_id + num_runs):
        runs.append(i)

    results = parse_files(kvs, runs, result_dir)

    table = PrettyTable()
    table.field_names = ["", "Memory utilization (GiB)", "Storage utilization (GiB)"]
    for kv in kvs:
        table.add_row([kv, results[kv]["mem"], results[kv]["storage"]])
    print(table)

main()