(*
 * A regression test.
 * Recursive operators that are declared via instances should not fail.
 *)
-------------------------------- MODULE Rec12 -------------------------------
EXTENDS Integers

----------------------------- MODULE inner ---------------------------
RECURSIVE A(_)
A(x) == IF x < 1 THEN x ELSE 1 + A(x - 1)
======================================================================

VARIABLES
    \* @type: Int;
    f

I == INSTANCE inner

UNROLL_DEFAULT_I_A == 0
UNROLL_TIMES_I_A == 5

Init == f = I!A(2)

Init2 == f = I!A(3)

Next == UNCHANGED f

Inv == f = 2
============================================================================

