-------------------------- MODULE ConfigUnsorted ----------------------------------------
(* A specification that introduces preprocessing issues *)
VARIABLES x

A == 1
B == 2
C == 3

\* the following annotations introduce a circular dependency
OVERRIDE_A == B
OVERRIDE_B == C
OVERRIDE_C == A

Init == x = 0
Next == UNCHANGED x
========================================================================================
