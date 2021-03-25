--------------------------- MODULE Rec1 -------------------------------------
(*
 * A test for unfolding recursive definitions.
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

UNROLL_TIMES_Fact == 8
UNROLL_DEFAULT_Fact == -1

Init ==
    f = Fact(4)

Next ==
    f' = Fact(7)

Inv ==
    f >= 1

=============================================================================
