--------------------------- MODULE Rec5 -------------------------------------
(*
 * A test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers, FiniteSets

MAX_POWER == 3              \* the maximal voting power
Procs == {"a", "b", "c"}     \* the set of processes

VARIABLES
    \* @type: Str -> Int;
    votingPower

RECURSIVE Sum(_)

Sum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE IN
    votingPower[x] + Sum(S \ {x})

UNROLL_TIMES_Sum == 3
UNROLL_DEFAULT_Sum == 0

Init ==
    votingPower \in [Procs -> 0..MAX_POWER]

Next ==
    votingPower' \in [Procs -> 0..MAX_POWER]

Inv ==
    Sum(Procs) < 10

=============================================================================
