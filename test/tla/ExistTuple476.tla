------------------ MODULE ExistTuple476 ----------------------
(* A regression test for the issue:
   https://github.com/informalsystems/apalache/issues/476
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init ==
    x = 0 /\ y = 0

Next ==
    \E <<i, j>> \in (1..2) \X (3..4):
        /\ x' = i
        /\ y' = j

==============================================================
