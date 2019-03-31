#!/usr/bin/env python3
#
# This script recursively finds the log files produced by apalache and TLC
# and collect them into a CSV file. It assumes that the directory layout
# is similar to the one produced by mk-script, that is:
#
# out/1/detailed.log
# out/2/tlc.out
# ...
#
# Igor Konnov, 2019

import argparse
import csv
import math
import os
import re
import sys

time_re = re.compile(r'elapsed_sec: (\d+)(|\.\d+) maxresident_kb: (\d+)')
timeout_re = re.compile(r'Command exited with non-zero status 124')
apalache_outcome_re = re.compile(r'The outcome is:\s*(.*)')
apalache_ntrans_re = re.compile(r'Found\s+(\d+)\s+initializing transitions and\s+(\d+)\s+next transitions')
apalache_depth_re = re.compile(r'Step\s+(\d+), level\s+\d+:')
tlc_no_error_re = re.compile(r'Model checking completed. No error has been found')
tlc_states_re = re.compile(r'\s(\d+)\s+distinct states found')
tlc_depth_re = re.compile(r'The depth of the complete state graph search is\s+(\d+)')
tlc_error_re = re.compile(r'Error:.* is violated')
tlc_progress_re =\
    re.compile(r'Progress\((\d+)\) at .*: (\d+) states generated (.*), (\d+) distinct states found')


def parse_options():
    parser = argparse.ArgumentParser(
            description="Parse the logs that are produced by the Apalache tests.")
    parser.add_argument("expDir", type=str,
       help="The directory where the scripts and experiments logs can be found.")
    parser.add_argument("--output", "-o", default='results.csv',
                        help="The filename of the output CSV file")
    args = parser.parse_args()
    args.expDir = os.path.realpath(args.expDir)
    return args


def collect_dirs(args):
    in_dir = os.path.join(args.expDir, "exp")
    print("Discovering the log files in %s" % in_dir)
    exp_descs = []
    files = list(os.listdir(in_dir))
    files.sort()
    for f in files:
        exp_path = os.path.join(in_dir, f)
        m = re.compile('\d+').match(f)
        if m and os.path.isdir(exp_path):
            if os.path.exists(os.path.join(exp_path, 'apalache.out')):
                print('  %3s -> apalache' % f)
                exp_descs.append({"no": int(f), "tool": "apalache", "path": exp_path})
            elif os.path.exists(os.path.join(exp_path, 'tlc.out')):
                print('  %3s -> tlc' % f)
                exp_descs.append({"no": int(f), "tool": "tlc", "path": exp_path})
            else:
                print('  %3s -> CORRUPTED' % f)

    return exp_descs


def parse_time(ed):
    entry = {'04:time_sec': None, '05:mem_kb': None, '03:status': 'Fail'}
    with open(os.path.join(ed['path'], 'time.out'), "r") as f:
        line = f.readline()
        while line:
            m = timeout_re.search(line)
            if m:
                entry = { **entry, '03:status': 'Timeout' }
            m = time_re.search(line)
            if m:
                entry = { **entry,
                    '04:time_sec': int(math.ceil(float(m.group(1)) + float(m.group(2)))),
                    '05:mem_kb': m.group(3)}

            line = f.readline()

    return entry


def parse_apalache(ed):
    entry = {'05:depth': 0, '10:ninit_trans': 0, '11:ninit_trans': 0}
    with open(os.path.join(ed['path'], 'detailed.log'), "r") as lf:
        line = lf.readline()
        while line:
            m = apalache_outcome_re.search(line)
            if m:
                entry['03:status'] = m.group(1) 
            m = apalache_depth_re.search(line)
            if m:
                entry['05:depth'] = int(m.group(1))
            m = apalache_ntrans_re.search(line)
            if m:
                entry['10:ninit_trans'] = m.group(1) 
                entry['11:ninit_trans'] = m.group(2) 

            line = lf.readline()

    prof_rule_re = re.compile(r'^(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)')
    ncells, nclauses, nclause_prod = 0, 0, 0
    with open(os.path.join(ed['path'], 'profile-rules.txt'), "r") as pf:
        line = pf.readline()
        while line:
            m = prof_rule_re.match(line)
            if m:
                ncells += int(m.group(3))
                nclauses += int(m.group(5))
                nclause_prod += int(m.group(5)) * int(m.group(6))
            line = pf.readline()

    avg_clause_len = math.ceil(nclause_prod / nclauses)
    entry = { **entry, '12:ncells': ncells,
                '13:nclauses': nclauses, '14:navg_clause_len': avg_clause_len }

    return entry


def parse_tlc(ed):
    entry = {'05:depth': 0, '20:nstates': 0}
    with open(os.path.join(ed['path'], 'tlc.out'), "r") as lf:
        line = lf.readline()
        while line:
            m = tlc_no_error_re.search(line)
            if m:
                entry['03:status'] = "NoError"

            m = tlc_error_re.search(line)
            if m:
                entry['03:status'] = "Error"

            m = tlc_progress_re.search(line)
            if m:
                entry['05:depth'] = int(m.group(1))
                entry['20:nstates'] = int(m.group(4))

            m = tlc_states_re.search(line)
            if m:
                entry['20:nstates'] = int(m.group(1))

            m = tlc_depth_re.search(line)
            if m:
                entry['05:depth'] = int(m.group(1))

            line = lf.readline()

    return entry


if __name__ == "__main__":
    args = parse_options()
    if not os.path.exists(args.expDir): 
        print("Error: Directory %s not found." % args.expDir)
        sys.exit(1)

    # collect the experimental results
    eds = collect_dirs(args)
    entries = []
    for ed in eds:
        entry = { '01:no': ed['no'], '02:tool': ed['tool'] }
        try:
            entry = { **entry, **parse_time(ed) } # merge
            if ed['tool'] == 'apalache':
                entry = { **entry, **parse_apalache(ed)}
            elif ed['tool'] == 'tlc':
                entry = { **entry, **parse_tlc(ed)}
            else:
                print('Unknown tool: ' + ed['tool'])
                entry['03:status'] = 'Fail'
        except FileNotFoundError as err:
            print("Error in %s: %s" % (ed['no'], err))
            entry['03:status'] = 'Fail'

        #print(entry)
        entries.append(entry)

    # collect the keys from the entries
    keys = set()
    for e in entries:
        keys = keys.union(set(e.keys()))

    sorted_keys = list(keys)
    sorted_keys.sort()

    # write the results to a csv file
    with open(args.output, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=sorted_keys, delimiter=',',
                            quotechar="'", quoting=csv.QUOTE_MINIMAL)
        writer.writeheader()
        for e in entries:
            writer.writerow(e)

    print("\n%d entries are written to {args.output}" % (len(entries)))

