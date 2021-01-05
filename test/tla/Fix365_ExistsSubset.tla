--------------------- MODULE Fix365_ExistsSubset ------------------------------
EXTENDS Integers, FiniteSets

VARIABLE S

Init ==
    S = {"a", "b", "c"}

Next ==
    \E X \in SUBSET S:
        /\ Cardinality(X) >= 2
        /\ S' = X

===============================================================================
