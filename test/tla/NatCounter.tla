----------------------------- MODULE NatCounter ------------------------
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    x

Init == x = 3

\* a natural counter can go below zero, and this is expected behavior
Next == x' = x - 1

Inv == x >= 0
========================================================================
