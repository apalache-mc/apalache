--------------------------- MODULE Slicer2 ------------------------------------
(* Testing slicing of symbolic transitions *)

VARIABLE state

Init ==
    state = "Init"

A ==
    state' = "A"

B ==
    \E x \in {1, 2, 3}:
        state' = "B"

Next ==
    A \/ B

Inv ==
    state /= "B"
===============================================================================
