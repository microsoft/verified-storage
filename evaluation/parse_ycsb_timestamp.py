import re
import csv

def parse_file(file_path):
    """Parse the file to extract workload information and throughput at each timestamp."""
    workload_data = {}
    current_workload = None
    command_line_pattern = re.compile(r'Command line: .*-P workloads/workload(\S+).*')
    zero_workload_pattern = re.compile(r'\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}:\d{3} (\d+) sec: 0 operations; est completion')
    workload_pattern = re.compile(r'\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}:\d{3} (\d+) sec: \d+ operations; (\d+\.\d+) current ops/sec;')
    load_pattern = re.compile(r'-load')

    with open(file_path, 'r') as file:
        for line in file:
            command_line_match = command_line_pattern.search(line)
            if command_line_match:
                workload = command_line_match.group(1)
                is_load = bool(load_pattern.search(line))
                if is_load:
                    current_workload = "load " + workload 
                else:
                    current_workload = workload 
                workload_data[current_workload] = {}
                continue

            if current_workload:
                throughput_match = workload_pattern.search(line)
                if throughput_match:
                    timestamp, throughput = throughput_match.groups()
                    throughput = float(throughput)

                    if timestamp not in workload_data[current_workload]:
                        workload_data[current_workload][timestamp] = []

                    workload_data[current_workload][timestamp].append(throughput)
                else:
                    throughput_match = zero_workload_pattern.search(line)
                    if throughput_match:
                        timestamp = throughput_match.groups()
                        timestamp = int(timestamp[0])

                        if timestamp not in workload_data[current_workload]:
                            workload_data[current_workload][timestamp] = []
                        # throughput is always 0 if we match this pattern
                        workload_data[current_workload][timestamp].append(0)


    return workload_data

def calculate_average_throughput(workload_data):
    """Calculate the average throughput for each timestamp in each workload."""
    average_throughput_data = {}
    for workload, timestamps in workload_data.items():
        average_throughput_data[workload] = {}
        for timestamp, throughputs in timestamps.items():
            average_throughput = sum(throughputs) / len(throughputs)
            average_throughput_data[workload][timestamp] = average_throughput
    return average_throughput_data

def write_to_csv(average_throughput_data, output_file):
    """Write the average throughput data to a CSV file."""
    with open(output_file, 'w', newline='') as csvfile:
        csvwriter = csv.writer(csvfile)
        csvwriter.writerow(['Workload', 'Timestamp', 'Average Throughput (ops/sec)'])
        for workload, timestamps in average_throughput_data.items():
            for timestamp, avg_throughput in timestamps.items():
                csvwriter.writerow([workload, timestamp, avg_throughput])

# Example usage
file_path = 'ycsb_output_pmemrocksdb'
output_file = 'ycsb_timing_pmemrocksdb.csv'
workload_data = parse_file(file_path)
average_throughput_data = calculate_average_throughput(workload_data)

write_to_csv(average_throughput_data, output_file)

for workload, timestamps in average_throughput_data.items():
    print(f"Workload {workload} :")
    for timestamp, avg_throughput in timestamps.items():
        print(f"  {timestamp}: {avg_throughput} ops/sec")