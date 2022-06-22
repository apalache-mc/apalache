---- MODULE BoxDiamond ----

\* Tests behaviour when a box operator is followed by a diamond operator

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init ==
    /\ x = 0
    /\ y = 1

Next ==
    /\ x' = y
    /\ y' = x

Liveness == []<>(x = 1 /\ y = 0)
FalseLiveness == []<>(x = 0 /\ y = 0)

====