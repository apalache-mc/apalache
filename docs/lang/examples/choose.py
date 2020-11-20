#!/usr/bin/env python3

# A fixed implementation of CHOOSE x \in S: TRUE
# that sorts the set by the string representation and picks the head 
def choose(s):
    lst = sorted([(str(e), e) for e in s], key=(lambda pair: pair[0]))
    (_, e) = lst[0]
    return e


if __name__ == "__main__":
    s = frozenset({ 1, 2, 3})
    print("CHOOSE {} = {}".format(s, choose(s)))
    s2 = frozenset({ frozenset({1}), frozenset({2}), frozenset({3})})
    print("CHOOSE {} = {}".format(s2, choose(s2)))

