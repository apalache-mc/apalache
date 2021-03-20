--------------------------- MODULE Rec2 -------------------------------------
(*
 * Another test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    size,
    \* @type: Set(Int);
    set

RECURSIVE Card(_)

\* this is very close to how cardinality is computed in Apalache
Card(S) ==
  IF S = {}
  THEN 0
  ELSE
    \* CHOOSE is introduced with a LET definition, to fix its value, whatever it may be
    \* Note that CHOOSE in APALACHE is non-deterministic and therefore
    \* S \ { CHOOSE x \in S : TRUE } leads to a false-positive C.E.
    LET x == CHOOSE y \in S: TRUE IN
    LET T == S \ {x} IN
    1 + Card(T)

\* unfold the operator Card up to 10 times
UNROLL_TIMES_Card == 10
\* on the 11th time, return just 0
UNROLL_DEFAULT_Card == 0

Init ==
    /\ set = {}
    /\ size = 0

Next ==
    /\ size' = size + 1
    /\ set' = set \union {size}

Inv == size = Card(set)

=============================================================================
