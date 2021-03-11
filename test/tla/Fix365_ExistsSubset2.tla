---------------------- MODULE Fix365_ExistsSubset2 ------------------------------
EXTENDS Integers, FiniteSets

Rounds == 0..2

VARIABLE
    \* @type: Int -> Set(Str);
    msgs

Init ==
    msgs \in [Rounds -> SUBSET {"a", "b", "c"}]

Next ==
    \E X \in (SUBSET msgs[2]):
        /\ Cardinality(X) >= 2
        /\ msgs' = [msgs EXCEPT ![2] = X]

===============================================================================
