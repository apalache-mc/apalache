------------------------- MODULE SkolemEmptyFunSet -------------------------
(*
 * Regression test: the membership of a skolemized \E f \in [S -> T] must not
 * become a global fact. The co-domain of the function set in Write is empty
 * once x = 2, and the execution Write (f[1] = 2), Start must not be lost.
 * See also issue #3503 for the same problem with \E c \in a..b.
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Str;
    pc

Init == x = 0 /\ pc = "a"

Write == x = 0 /\ \E f \in [{1} -> {y \in 1..2 : y > x}] : x' = f[1] /\ UNCHANGED pc

Start == pc = "a" /\ pc' = (IF x >= 1 THEN "b" ELSE "c") /\ UNCHANGED x

Next == Write \/ Start

\* violated by Write (f[1] = 2), then Start
Inv == ~(x = 2 /\ pc = "b")
=============================================================================
