----------------------------- MODULE InfDomFun ---------------------------
\* A regression test for functions with infinite domain, see:
\* https://github.com/informalsystems/apalache/issues/1798
EXTENDS Integers

VARIABLES
    \* @type: Int -> Int;
    f

Init == f = [[i \in Int |-> 0] EXCEPT ![0] = 42]

Next == UNCHANGED f

Inv == f[0] = 42

==========================================================================
