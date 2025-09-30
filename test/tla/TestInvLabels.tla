------------------------------- MODULE TestInvLabels --------------------------
EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    \/ Init0 :: x = 0
    \/ Init1 :: x = 1

Next ==
    \/ Next2 :: x' = 2
    \/ Next3 :: x' = 3

Inv ==
    /\ Inv2 :: x /= 2
    /\ Inv3 :: x /= 3
    /\ Inv4 :: x /= 4

V == x > 0
===============================================================================
