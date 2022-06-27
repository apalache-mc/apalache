---- MODULE Fairness ----

\* Tests behaviour when there are 
\* fairness operators.

EXTENDS Integers

VARIABLES
    \* @type: Int;
    x

Init ==
    /\ x = 0

IncrementX == x' = x + 1

DecrementX == x' = x - 1
    

Next ==
    IncrementX \/ DecrementX

Fairness ==
    WF_x(IncrementX)

LiveIfFair ==
    x > 5

FairnessImpliesLiveIfFair ==
    Fairness => LiveIfFair
    

====