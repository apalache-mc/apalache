-------------------------------- MODULE test6 -------------------------------
EXTENDS Integers

CONSTANT c

BHT == [height |-> Int, NextVS |-> Int]
SHT == [header |-> BHT, Commits |-> Int]

Init == c = BHT \/ c = SHT
Next == TRUE
=============================================================================