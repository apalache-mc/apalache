--------------------------- MODULE Rec3 -------------------------------------
(*
 * A test for unfolding recursive functions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES f

Fact[n \in Int] ==
  IF n <= 1
  THEN 1
  ELSE n * Fact[n - 1]

UNFOLD_TIMES_Fact == 5
UNFOLD_DEFAULT_Fact == -1

Init ==
    f = Fact[3]

Next ==
    f' = Fact[4]

Inv ==
    f >= 1

=============================================================================
