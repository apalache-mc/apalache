--------------------------- MODULE Rec3 -------------------------------------
(*
 * A test for handling recursive functions.
 * In this test, we compute the Fibonacci sequence in two ways:
 * (1) using an iterative computation, and (2) using a recursive function.
 *
 * Igor Konnov, April 2020
 *)
EXTENDS Integers

VARIABLES
    \* @type: Int;
    n,
    \* @type: Int;
    fibComp,
    \* @type: Int;
    fibCompPrev,
    \* @type: Int;
    fibSpec

\* the syntax for type annotations
a <: b == a

\* the type of the function Fib
FibT == [Int -> Int]

\* a recursive definition of the Fibonacci sequence
Fib[k \in 0..15] ==
  IF k <= 0
  THEN 0
  ELSE IF k <= 2
      THEN 1
      ELSE (Fib <: FibT)[k - 2] + (Fib <: FibT)[k - 1]

Init ==
    /\ n = 0
    /\ fibComp = 0
    /\ fibCompPrev = 1
    /\ fibSpec = Fib[n]

Next ==
    /\ n' = n + 1
    /\ fibCompPrev' = fibComp
    /\ fibComp' = fibComp + fibCompPrev
    /\ fibSpec' = Fib[n']

Inv ==
    fibSpec = fibComp

=============================================================================
