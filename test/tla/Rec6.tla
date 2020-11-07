--------- MODULE Rec6 -----------------
EXTENDS Integers

N == 5

VARIABLES set, count

RECURSIVE Sum(_)

Sum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN
    x + Sum(S \ {x})

UNROLL_DEFAULT_Sum == 0
UNROLL_TIMES_Sum == N

Init ==
  /\ set = {}
  /\ count = 0

Next ==
  \E x \in (1..N) \ set:
    /\ count' = count + x
    /\ set' = set \union {x}

Inv == count = Sum(set)
=======================================    

