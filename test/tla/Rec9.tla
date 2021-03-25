------------------------------ MODULE Rec9 ------------------------------------
(*
 * Computing set cardinality by using a recursive function.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers, FiniteSets

MAX_NUM == 5       \* the maximal number in the set
NUMS == 1..MAX_NUM  \* the set, from which the numbers are drawn

VARIABLES
    \* @type: Set(Int);
    set,
    \* @type: Int;
    size

(*
 The set cardinality function. It needs an upper bound on the set size.
 Although this function looks nice, be warned that this definition requires us
 to construct the powerset SUBSET NUMS and then write down the constraints
 for the function Card. This encoding is (at least) double-exponential.
 *)
Card[S \in SUBSET NUMS] ==
    IF S = {}
    THEN 0
    ELSE LET i == CHOOSE j \in S: TRUE IN
        1 + Card[S \ {i}]

Init ==
    /\ set = {}
    /\ size = 0

Next ==     
    \E i \in NUMS:
        /\ set' = set \union {i}
        /\ size' = Card[set']

Inv ==
   size = Cardinality(set)

===============================================================================
