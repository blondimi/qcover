# Copyright 2017 Michael Blondin, Alain Finkel, Christoph Haase, Serge Haddad

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
import argparse

def minimum(data):
    if len(data) == 0: return float("nan")

    return min(data)

def maximum(data):
    if len(data) == 0: return float("nan")

    return max(data)

def average(data):
    if len(data) == 0: return float("nan")

    return sum(data) / float(len(data))

def median(data):
    if len(data) == 0: return float("nan")

    sorted_data = sorted(data)
    size = len(sorted_data)
    half = size // 2

    if size % 2 == 1:
        return sorted_data[half]
    else:
        return (sorted_data[half-1] + sorted_data[half]) / 2.0

def output_summary(results):
    nb_results = len(results)
    status = [r[1] for r in results]
    time   = [r[2] for r in results]
    time_notimeout = [r[2] for r in results if r[1] != "Timeout"]

    print "* Timing *"
    print ""
    print "Smallest:             {:>9} ms".format(minimum(time))
    print "Median (w/ timeout):  {:>9.2f} ms".format(median(time_notimeout))
    print "Median:               {:>9.2f} ms".format(median(time))
    print "Average (w/ timeout): {:>9.2f} ms".format(average(time_notimeout))
    print "Average:              {:>9.2f} ms".format(average(time))
    print "Longest (w/ timeout): {:>9} ms".format(maximum(time_notimeout))
    print "Longest:              {:>9} ms".format(max(time))
    print "Total (w/ timeout):   {:>9} ms".format(sum(time_notimeout))
    print "Total:                {:>9} ms".format(sum(time))
    print ""
    print "* Results *"
    print ""
    print "Safe:    {:>4}/{}".format(status.count("Safe"),    nb_results) 
    print "Unsafe:  {:>4}/{}".format(status.count("Unsafe"),  nb_results) 
    print "Unknown: {:>4}/{}".format(status.count("Unknown"), nb_results) 
    print "Timeout: {:>4}/{}".format(status.count("Timeout"), nb_results) 

def summary(directories, mode, tool):
    results = []

    for i in range(len(directories)):
        res = []
        filename = "/results/{}.log".format(tool)

        with open(directories[i] + filename) as file_content:
            for row in file_content:
                args = row.strip().split(" ")
                res.append((args[0], args[1], int(args[2])))

        results.append(res)

    if mode == "overall":
        output_summary([item for r in results for item in r])
    else:
        for i in range(len(directories)):
            output_summary(results[i])

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Outputs results summary")

    parser.add_argument("directories", metavar="Directories",
                        type=str, nargs="+")
    
    parser.add_argument("--mode", dest="mode", action="store",
                default="all", help="all: output summary for all results. overall: output overall results.")

    parser.add_argument("--tool", dest="tool", action="store",
                default="tacas", help="tacas, petrinizer, mist-backward, bfc.")

    args = parser.parse_args()
    
    summary(args.directories, args.mode, args.tool)
