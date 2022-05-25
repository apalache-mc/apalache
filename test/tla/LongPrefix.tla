---- MODULE LongPrefix ----

\* tests behaviour when counterexamples have a nonempty 
\* non-looping prefix (the loop cannot start in the first state)

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    oldX,
    \* @type: Int;
    olderX

Range == {value \in Int: value >= 0 /\ value <= 50}

Init ==
    /\ x \in Range
    /\ oldX = -1
    /\ olderX = -2

Next ==
    /\ x' \in Range
    /\ oldX' = x
    /\ olderX' = oldX

Liveness == [](x = 0 => <>(olderX = 0))
FalseLiveness == [](x = 0 => <>(olderX = 1))

====