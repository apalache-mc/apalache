---- MODULE Fairness ----

\* Tests behaviour when there are 
\* fairness operators.

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

IncrementX == 
    x' = x + 1 /\ x < 3

DecrementX == 
    x' = x - 1 /\ x > -3

LeaveX ==
    UNCHANGED x
    

Next ==
    IncrementX \/ DecrementX \/ LeaveX

Fairness ==
    WF_x(IncrementX)

LiveIfFair ==
    <><<IncrementX>>_x

FairnessImpliesLiveIfFair ==
    Fairness => LiveIfFair
    

====