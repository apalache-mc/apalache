#!/usr/bin/env python3
#
# This script takes a CSV file with the description of benchmarks
# and sets up a directory to run the experiments in. It also generates
# the necessary scripts to run the experiments.
#
# Jure Kukovec, Igor Konnov, 2019

import argparse
import os
import shutil
import stat
import sys
import csv


dir = os.path.realpath( os.path.dirname(__file__) )

def os_specific_commands():
    if sys.platform.startswith("linux"):
        cmds = { "time": "/usr/bin/time", "timeout": "/usr/bin/timeout" }
    elif sys.platform == "darwin":
        cmds = { "time": "gtime", "timeout": "gtimeout" }
    else:
        print("Platform %s is not supported" % sys.platform)
        sys.exit(1)

    return cmds


os_cmds = os_specific_commands()


def parse_options():
    parser = argparse.ArgumentParser(description="Generate a script to run Apalache tests.")
    parser.add_argument("config", type=str,
            help="An input CSV that contains the parameters of the experiments")
    parser.add_argument("apalacheDir", type=str,
                        help="The APALACHE source code directory.")
    parser.add_argument("specDir", type=str,
                        help="The directory that contains the benchmarks.")
    parser.add_argument("outDir", type=str,
       help="The directory to write the scripts and outcome of the experiments.")
    args = parser.parse_args()
    args.apalacheDir = os.path.realpath(args.apalacheDir)
    args.specDir = os.path.realpath(args.specDir)
    args.outDir = os.path.realpath(args.outDir)
    return args


def tool_cmd(args, exp_dir, tla_filename, csv_row):
    def kv(key):
        return "--%s=%s" % (key, csv_row[key]) if csv_row[key].strip() != "" else ""

    tool = csv_row['tool']
    apalache_dir = args.apalacheDir
    ctime = os_cmds['time']
    ctimeout = "%s %s" % (os_cmds['timeout'], csv_row['timeout'])
    if tool == 'apalache':
        return "%s %s %s/bin/apalache-mc check %s %s %s %s %s &" \
                % (ctimeout, ctime,
                        args.apalacheDir, kv("init"),
                        kv("next"), kv("inv"), csv_row["args"], tla_filename)
    elif tool == 'tlc':
        # TLC needs a configuration file, it should be created by the user
        # figure out how to run tlc
        init, next, inv, args = kv("init"), kv("next"), kv("inv"), csv_row["args"]
        return f'{ctimeout} {ctime} java -cp {apalache_dir}/3rdparty/tla2tools.jar ' \
                + f' tlc2.TLC {args} {tla_filename} &'
    else:
        print("Unknown tool: %s" % tool)
        sys.exit(1)


def setup_experiment(args, row_num, csv_row):
    exp_dir = os.path.join(args.outDir, "%d" % row_num)
    os.makedirs(exp_dir)
    print("Populating the directory for the experiment %d:" % row_num)
    # As SANY is only looking for file in the current directory,
    # we have to copy all tla files in the experiment directory.
    # Note that filename may contain a directory name as well, e.g., paxos/Paxos.tla
    tla_full_filename = os.path.join(args.specDir, csv_row['filename'])
    tla_dir, tla_basename = os.path.split(tla_full_filename)
    for f in os.listdir(tla_dir):
        full_path = os.path.join(tla_dir, f)
        if os.path.isfile(full_path) and (f.endswith('.tla') or f.endswith('.cfg')):
            print(f"  copied {f}")
            shutil.copy(full_path, exp_dir)

    # create the script to run an individual experiment
    script = os.path.join(exp_dir, "run-one.sh")
    with open (script, "w+") as sf:
        lines = [
            '#!/bin/bash',
            'D=`dirname $0` && D=`cd "$D"; pwd` && cd "$D"',
            tool_cmd(args, exp_dir, tla_basename, csv_row),
            'pid="$!"',
            'trap \'kill $pid; exit 130\' INT # terminate the child process',
            'wait "$pid"',
            'exitcode="$?"',
            'echo "EXITCODE=$exitcode"',
            'exit "$exitcode"'
        ]
        for l in lines:
            sf.write(l)
            sf.write("\n")

    os.chmod(script, stat.S_IWRITE | stat.S_IREAD | stat.S_IEXEC)
    print(f'  created the script {script}')


if __name__ == "__main__":
    args = parse_options()
    if not os.path.exists(args.config): 
        print("Error: File %s does not exist." % args.config)
        sys.exit(1)

    with open(args.config, "r") as csvfile:
        sample = csvfile.read(1024)
        sniffer = csv.Sniffer()
        if not sniffer.has_header(sample):
            print("The input CSV file does not have a header")
            sys.exit(1)

        dialect = sniffer.sniff(sample)
        csvfile.seek(0)
        reader = csv.DictReader(csvfile, dialect=dialect)
        for (row_num, row) in enumerate(reader):
            setup_experiment(args, row_num, row)

