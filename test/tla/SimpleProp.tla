---- MODULE SimpleProp ----

\* Tests behaviour for very simple liveness properties

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

Next ==
    /\ x' = IF x = 3 THEN 0 ELSE x + 1

Liveness == <>(x > 2)
FalseLiveness == <>(x < 0)

====