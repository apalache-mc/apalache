--------------------------- MODULE Slicer3 ------------------------------------
(* Testing slicing of symbolic transitions *)

VARIABLE state

Init ==
    state = "Init"

A ==
    state' = "A"

B ==
    \E x \in {1, 2, 3}:
        LET C == { 4, 5, 6 }
        IN
        state' = "B"

Next ==
    A \/ B

Inv ==
    state /= "B"
===============================================================================
