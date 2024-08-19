import matplotlib.pyplot as plt
import matplotlib.pylab as pylab
import csv
import numpy as np
import sys
import math
import scipy.stats as st

append_sizes = [128, 256, 512, 1024, 4096, 8192, 65536, 131072, 262144]
append_size_strs = ["128B", "256B", "512B", "1KiB", "4KiB", "8KiB", "64KiB", "128KiB", "256KiB"]
append_size_strs = ["0.125", "0.25", "0.5", "1", "4", "8", "64", "128", "256"]

tests = ["pmdk", "old", "verif"]
test_names = ["PMDK", "initial", "latest"]

def plot(results_dir, mb_written):
    results = {t: {a: [] for a in append_sizes} for t in tests}
    for append_size in append_sizes:
        with open(results_dir + "/results_" + str(append_size) + ".csv", "r") as f:
            reader = csv.reader(f)
            for row in reader:
                results[row[0]][append_size].append(int(row[1]))

    params = {'figure.figsize': (8, 3)}
    pylab.rcParams.update(params)
    # params = {'figure.figsize': (8, 5)}
    # pylab.rcParams.update(params)

    sec = {t: {a: [i/1000000 for i in results[t][a]] for a in append_sizes} for t in tests}
    
    throughputs = {t: {a: [mb_written/i for i in sec[t][a]] for a in append_sizes} for t in tests}
    avg_throughput = {t: {a: np.average(throughputs[t][a]) for a in append_sizes} for t in tests}
    stddev = {t: {a: np.std(throughputs[t][a]) for a in append_sizes} for t in tests}

    conf_int = {t: {a: st.t.interval(0.95, df=len(throughputs[t][a])-1, loc=avg_throughput[t][a], scale=stddev[t][a]) for a in append_sizes} for t in tests}
    conf_int2 = {
        t: [
            [avg_throughput[t][a] - conf_int[t][a][0] for a in append_sizes],
            [conf_int[t][a][1] - avg_throughput[t][a] for a in append_sizes],
        ] for t in tests
    }

    x = np.arange(len(append_sizes))
    width = 0.25

    fig, ax = plt.subplots()
    ax.bar(x-width*1, avg_throughput["pmdk"].values(), width, yerr=conf_int2["pmdk"], hatch="\\\\", error_kw=dict(ecolor="red", capsize=2))
    ax.bar(x-width*0, avg_throughput["old"].values(), width, yerr=conf_int2["old"], hatch="..", error_kw=dict(ecolor="red", capsize=2))
    ax.bar(x+width*1, avg_throughput["verif"].values(), width, yerr=conf_int2["verif"], color="black", error_kw=dict(ecolor="red", capsize=2))

    plt.subplots_adjust(left=0.15, right=0.9, top=0.9, bottom=0.2)

    plt.yticks(fontsize=14)
    plt.xticks(x, append_size_strs, fontsize=14)
    plt.xlabel("Append size (KiB)", fontsize=18)
    plt.ylabel("Throughput (MiB/s)", fontsize=18)
    plt.legend(test_names, loc="upper left", fontsize=14)
    plt.savefig("results.pdf", format="pdf")

def main():
    if len(sys.argv) < 3:
        print("Too few arguments")
        exit(1)
    
    results = sys.argv[1]
    mb_written = int(sys.argv[2])

    plot(results, mb_written)

main()