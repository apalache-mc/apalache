------------------------ MODULE Test1425 -----------------------------
\* This test demonstrates an issue that appears in the original Bakery.
\* https://github.com/apalache-mc/apalache/issues/1425
EXTENDS Integers

VARIABLES
    \* @type: Int -> Set(Int);
    unchecked,
    \* @type: Int -> Int;
    nxt

Procs == 1..4    

Init ==
    /\ unchecked = [ p \in Procs |-> {} ]
    /\ nxt = [ p \in Procs |-> 1 ]

Next ==
    \/ \E self \in Procs:
        /\ \E i \in unchecked[self]:
            nxt' = [nxt EXCEPT ![self] = i]
        /\ nxt'[self] \in unchecked[self]
        /\ UNCHANGED unchecked
    \/ UNCHANGED <<unchecked, nxt>>
=====================================================================
