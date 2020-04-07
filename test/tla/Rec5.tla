--------------------------- MODULE Rec5 -------------------------------------
(*
 * A test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

CONSTANTS
    MAX_POWER,  \* a maximal voting power
    Procs       \* a set of processes

VARIABLES votingPower

a <: b == a

IntSet(S) == S <: {Int}

RECURSIVE Sum(_)

Sum(S) ==
  IF S = IntSet({})
  THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN
    votingPower[x] + Sum(S \ {x})

UNFOLD_TIMES_Sum == Cardinality(Procs)
UNFOLD_DEFAULT_Sum == 0

Init ==
    votingPower \in [Procs -> 0..MAX_POWER]

Next ==
    votingPower' \in [Procs -> 0..MAX_POWER]

=============================================================================
