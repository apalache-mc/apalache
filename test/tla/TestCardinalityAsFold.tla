(**
 * This test shows how one could use fold/reduce over a set to compute
 * set cardinality (over finite sets).
 *
 * Igor Konnov, 2026
 *)
---- MODULE TestCardinalityAsFold ----
EXTENDS Integers, FiniteSets, Apalache

VARIABLE
    \* @type: Set(Int);
    set

MyCardinality(S) ==
    LET \* @type: (Int, a) => Int;
        Add(n, elem) == n + 1
    IN
    ApaFoldSet(Add, 0, S)

Init ==
    \E T \in SUBSET (1..10):
        set = T

Next ==
    UNCHANGED set

Inv ==
    Cardinality(set) = MyCardinality(set)
======================================
