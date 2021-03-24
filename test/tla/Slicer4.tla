--------------------------- MODULE Slicer4 ------------------------------------
(* Testing slicing of symbolic transitions *)

VARIABLE
    \* @type: Str;
    state

Init ==
    state = "Init"

A ==
    state' = "A"

B ==
    \E x \in {1, 2, 3}:
        LET C == { 4, 5, 6 }
        IN
        \E y \in { 4, 5}:
            state' = "B"

Next ==
    A \/ B

Inv ==
    state /= "B"
===============================================================================
