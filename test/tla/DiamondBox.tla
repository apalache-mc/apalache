---- MODULE DiamondBox ----

\* Tests behaviour when a diamond operator is followed by a box operator

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
    /\ x' = IF y > 5 THEN 10 ELSE y + 1
    /\ y' = IF x > 5 THEN 10 ELSE x + 1

Liveness == <>[](x = 10)
FalseLiveness == <>[](x < 2)

====