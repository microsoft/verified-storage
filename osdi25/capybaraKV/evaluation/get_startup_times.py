
import argparse
import os
from prettytable import PrettyTable

kvstores = ["redis", "pmemrocksdb", "viper", "capybarakv"]
nice_kvstore_names = ["pmem-Redis", "pmem-RocksDB", "ViperDB", "CapybaraKV"]

def parse_files(result_dir, iterations):
    results = {kv: {"full": [], "empty": []} for kv in kvstores}
    for kv in kvstores:
        for i in range(0,iterations):
            # for some reason empty starts at 0 and full starts at 1. it doesn't 
            # really matter so just handle it here
            empty_file = os.path.join(result_dir, kv, "empty_setup", "Run" + str(i+1))
            full_file = os.path.join(result_dir, kv, "full_setup", "Run" + str(i))

            with open(empty_file, "r") as f:
                # each file only has one data point
                val = int(f.readlines()[0])
                results[kv]["empty"].append(val)
            if kv == "redis":
                # placeholder 
                results[kv]["full"].append(0)
            else: 
                with open(full_file, "r") as f:
                    # each file only has one data point
                    val = int(f.readlines()[0])
                    results[kv]["full"].append(val)

    avg_results = {kv: {"full": sum(results[kv]["full"])/iterations, "empty": sum(results[kv]["empty"])/iterations} for kv in kvstores}

    return avg_results

def parse_arguments():
    parser = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    parser.add_argument('result_dir', 
                       help='Directory containing microbenchmark output data')
    parser.add_argument("-i", "--iterations",
                        help="Number of iterations used in the experiment",
                        default=5)

    return parser.parse_args()

def main():
    args = parse_arguments()

    results = parse_files(args.result_dir, args.iterations)
    
    table = PrettyTable()
    table.field_names = ["", "Empty setup (ms)", "Full setup (ms)"]
    for kv in kvstores:
        if kv == "redis":
            table.add_row([kv, round(results[kv]["empty"]/1000), "--"])
        else:
            table.add_row([kv, round(results[kv]["empty"]/1000), round(results[kv]["full"]/1000)])
    print(table)

main()