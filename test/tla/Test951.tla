------------------------------ MODULE Test951 --------------------------------
EXTENDS Apalache, Integers, FiniteSets, Sequences, TLC
VARIABLES 
    \* @type: Int -> Int;
    myfun

Init ==
    myfun = [e \in 1..3 |-> e]

Next ==
    myfun' = myfun @@ [e \in 2..4 |-> 42]

Inv == 
    /\ myfun[2] = 2
    /\ myfun[3] = 3
==============================================================================
