----------------------------- MODULE Rand -----------------------------------
EXTENDS Integers, FiniteSets

VARIABLE S

Init ==
    /\ S \in SUBSET (1..10)
    /\ Cardinality(S) >= 5

Next ==
    \/ \E x \in S:
         x % 2 = 0 /\ S' = (S \ { x }) \union { x + x }
    \/ \E x \in S:
         x % 2 /= 0 /\ S' = S \ { x }

Inv ==
    \E x \in S: x > 0

=============================================================================
