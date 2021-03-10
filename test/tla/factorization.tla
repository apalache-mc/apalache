-------------------- MODULE factorization ----------------------------
(*
 A simple example of factorization.
 This example works fast in Apalache, but it takes ages with TLC.
 *)

EXTENDS Integers

VARIABLE
    \* @type: Int;
    m,
    \* @type: Int;
    n,
    \* @type: Bool;
    answer

Init ==
    m = 0 /\ n = 0 /\ answer = FALSE

Next ==
    \E i, j \in 2..1000000:
        /\ i * j = 999999
        /\ m' = i
        /\ n' = j
        /\ answer' = TRUE

Inv ==
    answer = FALSE
======================================================================
