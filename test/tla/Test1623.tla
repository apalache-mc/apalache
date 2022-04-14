------------------ MODULE Test1623 ---------------------------            
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

ASSUME (N \in Nat)

VARIABLE
    \* @type: Int;
    x

Init ==
    x = N

Next ==
    \/ x > 0 /\ x' = x - 1
    \/ x = 0 /\ UNCHANGED x

Inv ==
    x >= 0
=====================================================================