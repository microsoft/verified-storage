import matplotlib.pyplot as plt
import matplotlib.pylab as pylab
import csv
import numpy as np
import sys
import math

append_sizes = [128, 512, 1024, 4096, 8192, 65536, 131072, 262144]
tests = ["pmdk", "verif"]

def plot(results_directory, mb_written):
    # results = {a:{t:[] for t in tests} for a in append_sizes}
    results = {t: {a: [] for a in append_sizes} for t in tests}
    for append_size in append_sizes:
        with open(results_directory + "/results_" + str(append_size) + ".csv", "r") as f:
            reader = csv.reader(f)
            for row in reader:
                results[row[0]][append_size].append(int(row[1]))

    params = {'figure.figsize': (6.4, 3)}
    pylab.rcParams.update(params)

    # take average and convert from usec to sec so that we can easily compute mb/sec
    avgs = {t: {a: np.average(results[t][a])/1000000 for a in append_sizes} for t in tests}
    # mb_written/avg gives mb/sec
    throughput = {t: {a: mb_written/avgs[t][a] for a in append_sizes} for t in tests}

    x = np.arange(len(append_sizes))
    width = 0.4

    fig, ax = plt.subplots()
    ax.bar(x-width*0.5, throughput["pmdk"].values(), width)
    ax.bar(x+width*0.5, throughput["verif"].values(), width)

    plt.subplots_adjust(left=0.15, right=0.9, top=0.9, bottom=0.2)


    labels = [str(a) for a in append_sizes]
    plt.yticks(fontsize=12)
    plt.xticks(x, labels, fontsize=12)
    plt.xlabel("Append size", fontsize=14)
    plt.ylabel("Throughput (MiB/s)", fontsize=14)
    plt.legend(tests)
    plt.savefig("results.pdf", format="pdf")


def main():
    if len(sys.argv) < 3:
        print("Too few arguments")
        exit(1)
    results_directory = sys.argv[1]
    mb_written = int(sys.argv[2])

    plot(results_directory, mb_written)

main()

