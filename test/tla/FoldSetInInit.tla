---------------------------- MODULE FoldSetInInit -----------------------------
\* regression test for FoldSet in Init, Next, and Inv
EXTENDS Integers, Apalache

N == 10

VARIABLES
    \* @type: Set(Int);
    values

Sum(S) ==
    LET Add(i, j) == i + j IN
    FoldSet(Add, 0, S)

Init ==
    \E S \in SUBSET (1..N):
        /\ Sum(S) = N
        /\ values := S

Next ==
    \E S \in SUBSET (1..N):
        /\ Sum(S) < Sum(values)
        /\ values' := S
    
Inv ==
    2 * Sum(values) <= N * (N + 1)

===============================================================================
