--------------- MODULE NonNullaryLet ----------------
EXTENDS Integers
VARIABLE n

Foo == LET r(x) == TRUE IN r(1)

Init == n = 0

Next == Foo /\ n' = 1
===========================================