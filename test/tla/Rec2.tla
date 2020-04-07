--------------------------- MODULE Rec2 -------------------------------------
(*
 * Another test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES size, set

a <: b == a
IntSet(S) == S <: {Int}

RECURSIVE Card(_)

\* this is very close to how cardinality is computed in Apalache
Card(S) ==
  IF S = IntSet({})
  THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE IN
    1 + Card(S \ {x})

\* unfold the operator Card up to 10 times
UNFOLD_TIMES_Card == 10
\* on the 11th time, return just 0
UNFOLD_DEFAULT_Card == 0

Init ==
    /\ set = IntSet({})
    /\ size = 0

Next ==
    /\ size' = size + 1
    /\ set' = set \union {size}

Inv == size = Card(set)

=============================================================================
