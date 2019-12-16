--------------- MODULE test2 -------------
EXTENDS Integers
CONSTANT x

Init == x.c = "a" /\ x.d = 2
Next == TRUE
============================================