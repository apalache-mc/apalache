---- MODULE QuantifiersInEnabled ----

\* Tests behaviour when there are 
\* superfluous box operators in the formula

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

Next ==
    /\ \E i \in 1..5: x' = i
    /\ x' >= 0

Liveness == <>(<<ENABLED Next>>_x)

====