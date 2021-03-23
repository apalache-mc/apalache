--------------------------- MODULE Rec11 -------------------------------------
(*
 * Testing whether Unroller complains about missing UNROLL_TIMES_Fact.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    f

RECURSIVE Fact(_)

Fact(n) ==
  IF n <= 1
  THEN 1
  ELSE n * Fact(n - 1)

\* define the default value
UNROLL_DEFAULT_Fact == 0

\* but keep UNROLL_TIMES_Fact undefined
\*UNROLL_TIMES_Fact == 4

Init ==
    f = Fact(4)

Next ==
    f' = Fact(7)

Inv ==
    f >= 1

=============================================================================
