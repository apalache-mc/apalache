------------------------- MODULE UnchangedAsInv1663 ---------------------------
EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

Next ==
    \/ x < 0 /\ x' = x + 1
    \/ x >= 0 /\ UNCHANGED x

Inv ==
    UNCHANGED x

===============================================================================
