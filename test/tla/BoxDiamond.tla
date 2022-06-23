---- MODULE BoxDiamond ----

\* Tests behaviour when a box operator is followed by a diamond operator

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

Next ==
    /\ x' = IF x = 3 THEN 0 ELSE x + 1

Liveness == []<>(x = 1)
FalseLiveness == <>[](x = 0)

====