------------------------ MODULE UnchangedExpr471 ----------------------------
(* A regression test for UNCHANGED e:
   see issue: https://github.com/informalsystems/apalache/issues/471
 *)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Int;
    f,
    \* @type: Int;
    i

ConstInit ==
    N' = 3

Init ==
    /\ f = [ j \in 1..3 |-> j * 2]
    /\ i = 2

Next ==
    UNCHANGED <<f, i, f[i], N>>

==============================================================================

