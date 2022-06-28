-------------------------------- MODULE Bug1880 --------------------------------
EXTENDS FiniteSets

VARIABLES
    \* @type: Set(Int);
    set

Init ==
    LET \* @type: () => Set(a);
        Empty == {}
    IN
    set = Empty

Next == UNCHANGED set
===============================================================================
