------------------------- MODULE SkolemEmptyRange -------------------------
(*
 * Regression test: the bounds of a skolemized \E c \in a..b must not become
 * global facts. The range of the existential in Write is empty once x = 2,
 * and the execution Write (c = 2), Start must not be lost.
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Str;
    pc

Init == x = 0 /\ pc = "a"

Write == x = 0 /\ \E c \in 1..(2 - x) : x' = c /\ UNCHANGED pc

Start == pc = "a" /\ pc' = (IF x >= 1 THEN "b" ELSE "c") /\ UNCHANGED x

Next == Write \/ Start

\* violated by Write (c = 2), then Start
Inv == ~(x = 2 /\ pc = "b")
=============================================================================
