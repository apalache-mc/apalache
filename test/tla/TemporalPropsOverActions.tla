---- MODULE TemporalPropsOverActions ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

IncrementX == x' = IF x < 3 THEN x + 1 ELSE 0
DecrementX == x > 0 /\ x' = x - 1

Next ==
    IncrementX \/ DecrementX
    
Liveness ==
    <>(<<x' = x>>_x)

FalseLiveness ==
    ([DecrementX]_x)
====