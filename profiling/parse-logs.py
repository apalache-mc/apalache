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

time_re = re.compile(r'(\d+\.\d+)user\s+(\d+\.\d+)system.*?(\d+)maxresident')
outcome_re = re.compile(r'^.*The outcome is:\s*(.*)$')
ntrans_re = re.compile(r'^.*Found\s+(\d+)\s+initializing transitions and\s+(\d+)\s+next transitions')


def parse_options():
    parser = argparse.ArgumentParser(
            description="Parse the logs that are produced by the Apalache tests.")
    parser.add_argument("expDir", type=str,
       help="The directory where the scripts and experiments logs can be found.")
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
    with open(os.path.join(ed['path'], 'time.out'), "r") as f:
        m = time_re.match(f.readline())
        if m:
            return {'time_sec': int(math.ceil(float(m.group(1)) + float(m.group(2)))),
                    'mem_kb': m.group(3)}
        else:
            return {'time_sec': None, 'mem_kb': None}

        


def parse_apalache(ed):
    entry = {}
    with open(os.path.join(ed['path'], 'detailed.log'), "r") as lf:
        line = lf.readline()
        while line:
            m = outcome_re.match(line)
            if m:
                entry['status'] = m.group(1) 
            m = ntrans_re.match(line)
            if m:
                entry['ninit_trans'] = m.group(1) 
                entry['nnext_trans'] = m.group(2) 

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
    entry = { **entry, "ncells": ncells,
                "nclauses": nclauses, "avg_clause_len": avg_clause_len }

    return entry


def parse_tlc(ed):
    return {}


if __name__ == "__main__":
    args = parse_options()
    if not os.path.exists(args.expDir): 
        print("Error: Directory %s not found." % args.expDir)
        sys.exit(1)

    eds = collect_dirs(args)
    for ed in eds:
        entry = { 'no': ed['no'], 'tool': ed['tool'] }
        try:
            entry = { **entry, **parse_time(ed) } # merge
            if ed['tool'] == 'apalache':
                entry = { **entry, **parse_apalache(ed)}
            elif ed['tool'] == 'tlc':
                entry = { **entry, **parse_tlc(ed)}
            else:
                print('Unknown tool: ' + ed['tool'])
                entry['status'] = 'Failure'
        except FileNotFoundError as err:
            print(f"Error in {ed['no']}: {err}")
            entry['status'] = 'failure'

        print(entry)

