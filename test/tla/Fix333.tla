------------------------- MODULE Fix333 -----------------------------------
VARIABLES
    \* @type: Bool;
    error

Init ==
    error = FALSE

Next ==
    error' = FALSE

Inv ==
    ~(error = TRUE)
===========================================================================
