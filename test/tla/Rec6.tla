--------- MODULE Rec6 -----------------
EXTENDS Integers

CONSTANTS N
VARIABLES set, count

RECURSIVE Sum(_)

Sum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE x \in S: TRUE IN
    x + Sum(S \ {x})

Init ==
  /\ set = {}
  /\ count = 0

Next ==
  \E x \in (1..N) \ set:
    /\ count' = count + x
    /\ set' = set \union {x}

Inv == count = Sum(set)
=======================================    

