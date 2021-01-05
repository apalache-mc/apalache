----------------------- MODULE ConfigReplacements -----------------------------
VARIABLES x

Value == 0

Value2 == 2

Init ==
    /\ x = Value

Next ==
    UNCHANGED x

Inv ==
    x = 2

===============================================================================
