import csv
import sys
import os
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import pprint

thread_counts = [1, 2, 4, 8, 16]
workloads = ['Loada', 'Runa', 'Runb', 'Runc', 'Rund', 'Runf', 'Loadx', 'Runx', "Runy", "Runz"]
workload_titles = ['LoadA', 'RunA', 'RunB', 'RunC', 'RunD', 'RunF', 'LoadX', 'RunX', 'RunY', 'RunZ']
nice_names = {"redis": "pmem-Redis", "pmemrocksdb": "pmem-RocksDB", "viper": "Viper", "capybarakv": "CapybaraKV"}

matplotlib.rcParams['pdf.fonttype'] = 42
matplotlib.rcParams['ps.fonttype'] = 42

def parse_data(fs, runs, result_dir):
    raw_results = {w: {} for w in workloads}
    avg_results = {w: {} for w in workloads}

    # read in all data
    for w in workloads:
        for t in thread_counts:
            raw_results[w][t] = {}
            for f in fs:
                run_dir = os.path.join(result_dir, "threads_" + str(t), f, w)
                raw_results[w][t][f] = []

                for i in runs:
                   run_file = os.path.join(run_dir, "Run" + str(i))
                   with open(run_file, "r") as fp:
                       lines = fp.readlines()
                       for line in lines:
                           if "(ops/sec)" in line:
                               words = line.split()
                               perf = round(float(words[2]), 2)
                               raw_results[w][t][f].append(perf)
    
    # take the average of each workload at each number of threads
    for w in workloads:
        for t in thread_counts:
            avg_results[w][t] = []
            for f in fs:
                avg_results[w][t].append(sum(raw_results[w][t][f]) / len(raw_results[w][t][f]))

    return avg_results


def plot_data_single_fig(fs, avg_results, output_file):
    plt.plot()

    values = []
    for t in thread_counts:
        thread_vals = []
        for w in workloads:
            thread_vals.append(avg_results[w][t][0] / 1000000)
        values.append(thread_vals)

    fig, ax = plt.subplots()

    color_cycle = plt.rcParams['axes.prop_cycle'].by_key()['color']
    ax.set_prop_cycle(
        color=color_cycle+["black"], 
        marker=["o", "x", "s", "d", "+", "v", "^", "p", ".", "o", "x"],
        linestyle=["-", "-", "-", "-", "-", "-", "--", "--", "--", "--", "--"]
    )
    ax.plot(thread_counts, values)
    ax.set_xticks(thread_counts)
    leg = ax.legend(workload_titles, loc="upper center", ncol=5, bbox_to_anchor=(0.46, 1.5), fontsize="8") #bbox_to_anchor=(1.75, 0.5), ncol=2)
    leg.get_frame().set_alpha(0)
    ax.set_xlabel("Thread count")
    ax.set_ylabel("Througput (Mops/s)")
    

    fig.set_figwidth(4.5)
    fig.set_figheight(2.6)
    fig.tight_layout(pad=0.5)
    ax.grid(True, zorder=0, axis="y")
    # plt.gca().yscale("log")
    # plt.yscale("log")
    # plt.yticks([500,1000,1500,2000,2500,3000,3500,4000])
    # formatter = matplotlib.ticker.ScalarFormatter()
    # formatter.set_powerlimits((0,3))
    # plt.gca().yaxis.set_major_formatter(formatter)
    

    plt.savefig(output_file, format="pdf", bbox_inches="tight")


def main():
    if len(sys.argv) < 4:
        print("Usage: python3 plot_fig4.py <num_runs> <start_run_id> <result_dir> <output_file>")
        return

    args = sys.argv[1:]

    fs = ["capybarakv"]
    fs_nice = [nice_names[f] for f in fs]

    num_runs = int(args[0])
    start_run_id = int(args[1])
    result_dir = args[2]
    output_file = args[3]

    runs = []
    for i in range(start_run_id, start_run_id + num_runs):
        runs.append(i)

    avg_results = parse_data(fs, runs, result_dir)
    plot_data_single_fig(fs_nice, avg_results, output_file)

main()