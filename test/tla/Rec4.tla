--------------------------- MODULE Rec4 -------------------------------------
(*
 * A test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES f

RECURSIVE Fib(_)

Fib(n) ==
  IF n <= 0
  THEN 0
  ELSE IF n <= 2
      THEN 1
      ELSE Fib(n - 2) + Fib(n - 1)

UNFOLD_TIMES_Fib == 5
UNFOLD_DEFAULT_Fib == -1

Init ==
    f = Fib(3)

Next ==
    f' = Fib(4)

Inv ==
    f >= 1

=============================================================================
