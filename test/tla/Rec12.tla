(*
 * A regression test.
 * Recursive operators that are declared via instances should not fail.
 *)
-------------------------------- MODULE Rec12 -------------------------------
----------------------------- MODULE inner ---------------------------
RECURSIVE A(_)
A(x) == IF x = 1 THEN 1 ELSE A(1)
======================================================================

VARIABLES f
I == INSTANCE inner

Init == f = I!A(0)

Next == UNCHANGED f

Inv == TRUE
============================================================================

