---- MODULE Enabled ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

IncrementX == x' = x +1
DecrementX == x > 0 /\ x' = x - 1

Next ==
    IncrementX \/ DecrementX
    


Liveness ==
    <>(<<IncrementX>>_x)

FalseLiveness ==
    []([DecrementX]_x)

====