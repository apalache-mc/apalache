------------------------ MODULE ExistsAsValue -------------------------
\* a test for the issue #148
VARIABLES x

Init ==
    x = TRUE

Next ==
    x' = \E y \in {1, 2}: y /= 1

Next2 ==
    IF \E y \in {1, 2}: y /= 1
    THEN x' = TRUE
    ELSE x' = FALSE

Inv == x
=======================================================================
