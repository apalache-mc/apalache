#!/usr/bin/env python3

import functools

def subset(s):
    """construct the set of all subsets, that is, SUBSET S"""
    sets = []           # sets to be constructed
    carrier = list(s)
    nelems = len(carrier)
    bits = [0] * nelems # the binary vector encodes a set under construction
    current = set()     # a set under cosntruction
    sets.append(frozenset(current))     # add {}

    while True:
        # turn leading 1s into 0s, add elements until 0 is found
        leading0 = -1
        for i in range(0, nelems):
            if bits[i] == 0:
                leading0 = i
                break
            else:
                bits[i] = 0
                current.remove(carrier[i])

        if leading0 < 0:
            # all bits were set to 1, end of the loop
            return frozenset(sets)
        else:
            # set 0 to 1
            bits[leading0] = 1
            # add the element to the current set
            current.add(carrier[leading0])
            # add the set
            sets.append(frozenset(current))


def union(s):
    """Flatten the set, that is, implement UNION S"""
        
    return functools.reduce(lambda x, y: x | y, s, frozenset())

if __name__ == "__main__":
    carrier = frozenset({"a", "b", "c", "d"})
    print("SUBSET {}".format(carrier))
    powerset = subset(carrier)
    for s in powerset:
        print(s)

    print("UNION (SUBSET {})".format(carrier))
    print(union(powerset))

