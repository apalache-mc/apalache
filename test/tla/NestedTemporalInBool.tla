---- MODULE NestedTemporalInBool ----

\* Tests behaviour when boolean and temporal operators are mixed

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

Liveness == []<>(x = 1) /\ [](y < 1 \/ <>(y = 1)) /\ ~<>[](x > 5)
FalseLiveness == []<>(x = 1) /\ [](y < 1 \/ <>(y = 1)) /\ <>[](x > 5)

====