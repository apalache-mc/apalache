--------------------------- MODULE Rec11 -------------------------------------
(*
 * A test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES f

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
