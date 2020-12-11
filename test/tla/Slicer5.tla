--------------------------- MODULE Slicer5 ------------------------------------
(* Testing slicing of symbolic transitions *)
EXTENDS Integers, FiniteSets

VARIABLE state, n, k

Init ==
    /\ state = "Init"
    /\ n' = 0
    /\ k' = 2

Start ==
    /\ "foo" /= "bar"  
    /\ state /= "C"
    /\ state' = "B"

A ==
    /\ state' = "A"
    /\ n' = 1
    /\ k' = 3

B ==
    \E x \in {1, 2, 3}:
        LET C == { 4, 5, 6 } IN
        LET D == { 7, 8 } IN
        Cardinality(C) >= 2
            /\ (\E y \in SUBSET { 4, 5}:
              /\ x = 2
                  /\ k' = 4
                  /\ Start
                  /\ UNCHANGED n)

Next ==
    A \/ B

Inv ==
    state /= "B"
===============================================================================
