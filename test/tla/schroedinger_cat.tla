------------------------- MODULE schroedinger_cat ----------------------------
VARIABLE state
Init == state = "ALIVE"
Next == state' = state \/ state' = "DEAD"
Inv == state = "ALIVE"
==============================================================================
