#!/usr/bin/env python

import re
import sys

RULE_BEGIN_RE = re.compile("^; ([A-Za-z]*Rule)(\(.*\)) \{.*")
RULE_END_RE = re.compile("^; \} ([A-Za-z]*Rule).*")
TIME_RE = re.compile("^;.*@@ TIME TO SAT: ([0-9]{5,5})\.([0-9]{9,9}) sec @@.*")


class Rule:
    def __init__(self, name, body):
        self.name = name
        self.body = body
        self.children = []
        self.self_sec = 0
        self.cumu_sec = 0

    def accumulate_time(self):
        self.cumu_sec = self.self_sec 
        for c in self.children:
            self.cumu_sec += c.cumu_sec


class RuleSummary:
    def __init__(self, name, self_sec, cumu_sec, ncalls):
        self.name = name
        self.self_sec = self_sec
        self.cumu_sec = cumu_sec
        self.ncalls = ncalls
        self.percentage = 0

    def self_per_call_sec(self):
        return self.self_sec / self.ncalls

    def cumu_per_call_sec(self):
        return self.cumu_sec / self.ncalls


def summary_cumu_sec(r):
    return r.cumu_sec


def read_log(filename):
    top_rules = []
    stack = []
    with open(filename, 'r') as f:
        for line in f:
            m = RULE_BEGIN_RE.match(line)
            if m:
                r = Rule(m.group(1), m.group(2))
                stack.append(r)
                continue

            m = RULE_END_RE.match(line)
            if m:
                name = m.group(1)
                r = stack.pop()
                assert(r.name == name)
                r.accumulate_time()
                if stack != []:
                    stack[-1].children.append(r)
                else:
                    top_rules.append(r)
                continue

            m = TIME_RE.match(line)
            if m:
                sec = float(m.group(1))
                ns = float(m.group(2))
                if stack != []:
                    stack[-1].self_sec += sec + ns / 1000000000.

    return top_rules


def collect(rules):
    sums = {}

    def each_rule(r):
        try:
            s = sums[r.name]
        except KeyError, _:
            s = RuleSummary(r.name, 0, 0, 0)
            sums[r.name] = s

        s.ncalls += 1
        s.self_sec += r.self_sec
        s.cumu_sec += r.cumu_sec
        for c in r.children:
            each_rule(c)
    
    for r in rules:
        each_rule(r)

    total_sec = 0.0
    for s in sums.values():
        total_sec += s.cumu_sec

    print "Total: %-7.2f sec" % total_sec

    for s in sums.values():
        if total_sec > 0.000000001:
            s.percentage = 100 * s.cumu_sec / total_sec
        else:
            s.percentage = 0

    return sums


if __name__ == "__main__":
    argv = sys.argv[1:]
    if len(argv) < 1:
        print "Use: %s log.smt" % sys.argv[0]
        sys.exit(1)

    top_rules = read_log(argv[0])
    sums = collect(top_rules)
    sorted_sums = sorted(sums.values(), key=summary_cumu_sec, reverse=True)
    print " %    cumulative   self               self      total"
    print "time   seconds    seconds     calls  ms/call   ms/call       name"
    for s in sorted_sums:
        print "{:3.2f}    {:7.2f}    {:7.2f}    {:5d}  {:7.2f}    {:7.2f}    {:s}"\
                .format(s.percentage, s.cumu_sec, s.self_sec, s.ncalls,
                   s.self_per_call_sec(), s.cumu_per_call_sec(), s.name)


