--------------------------- MODULE Slicer1 ------------------------------------
(* Testing slicing of symbolic transitions *)

VARIABLE
    \* @type: Str;
    state

Init ==
    state = "Init"

A ==
    state' = "A"

B ==
    state' = "B"

Next ==
    A \/ B

Inv ==
    state /= "B"
===============================================================================
