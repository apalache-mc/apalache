#!/usr/bin/env python
#
# Extract the TLAPS tests that were designed for TLC.
#
# Use: ./extract-tlaps-tests.py $TLAPS/tlatools/test-model/suite
#
# Igor Konnov, 2018

import os
import os.path
import re
import sys

INV_RE = re.compile(r'^\s*Inv\s*==.*$')
CLAUSE_RE = re.compile(r'^\s*/\\.*$')
END_RE = re.compile(r'^=+\s*$')
SPACE_RE = re.compile(r'^\s*$')

def filter_inv(filename, clause_no, prefix):
    in_inv = False
    in_clause = False
    asserts = 0
    with open(prefix, 'w') as fo:
        with open(filename, 'r') as fi:
            for line in fi:
                if INV_RE.match(line):
                    in_inv = True
                elif in_inv and CLAUSE_RE.match(line):
                    in_clause = True
                elif in_inv and SPACE_RE.match(line):
                    asserts += 1 # start the next assertion
                    in_clause = False
                elif END_RE.match(line):
                    in_inv = False

                if not in_inv or not in_clause:
                    fo.write(line)
                else:
                    if asserts == clause_no:
                        fo.write(line)
                    else:
                        fo.write("\\* " + line)

    return asserts


def extract(dirname, filename):
    (prefix, _) = os.path.splitext(filename)
    def filt(no):
        return filter_inv(os.path.join(dirname, filename),
                          no,
                          "%s-%d.tla" % (prefix, no))

    asserts_cnt = filt(0)
    if asserts_cnt > 0:
        for clause_no in range(1, asserts_cnt):
            filt(clause_no)
    # else: there are no assertions to extract, keep this file as a single test

    print "%s: extracted %d tests" % (prefix, asserts_cnt)


if __name__ == "__main__":
    suite_dir = sys.argv[1]
    for _, _, files in os.walk(suite_dir):
        for f in files:
            if f.endswith('.tla'):
                extract(suite_dir, f)

