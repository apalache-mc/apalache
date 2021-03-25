--------------------------- MODULE Rec4 -------------------------------------
(*
 * A test for unfolding recursive definitions.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    f

RECURSIVE Fib(_)

Fib(n) ==
  IF n <= 0
  THEN 0
  ELSE IF n <= 2
      THEN 1
      ELSE Fib(n - 2) + Fib(n - 1)

UNROLL_TIMES_Fib == 6
UNROLL_DEFAULT_Fib == -1

Init ==
    f = Fib(4)

Next ==
    f' = Fib(5)

Inv ==
    f >= 1

=============================================================================
