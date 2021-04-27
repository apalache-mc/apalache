------------------------- MODULE schroedinger_cat ----------------------------
VARIABLE
    \* @type: Str;
    state

Init == state = "ALIVE"
Next == state' = state \/ state' = "DEAD"
Inv == state = "ALIVE"
==============================================================================
