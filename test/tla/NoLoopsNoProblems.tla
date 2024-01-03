---- MODULE NoLoopsNoProblems ----

\* Tests behaviour when the system does not have loops

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Range == {value \in Int: value >= 0 /\ value <= 50}

Init ==
    /\ x \in Range
    /\ y  \in Range
    /\ x # y

Next ==
    /\ x' = y + 1
    /\ y' = x + 1

Liveness == [](x > 50 => <>([](y > 50)))
FalseLiveness == <>(x > 52) => [](y > 100) 

====