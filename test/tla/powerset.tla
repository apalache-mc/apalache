---------------------------- MODULE powerset ----------------------------
EXTENDS Integers

VARIABLE
    \* @type: Set(Int);
    S

Init ==
    /\ S \in SUBSET (1..50)
    /\ 5 \notin S

Next ==
    \/ \E x \in S:
        S' = S \ {x}
    \/ UNCHANGED S

Inv ==
    5 \notin S

=========================================================================
