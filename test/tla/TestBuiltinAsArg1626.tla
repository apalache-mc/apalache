------------------------- MODULE TestBuiltinAsArg1626 -------------------------
(**
  * A regression test for passing built-in operators as arguments.
  * For details, see: https://github.com/apalache-mc/apalache/issues/1626
  *)
EXTENDS Integers

Sum(F(_, _), x, y) == F(x, y)

IsMem(e, set) == e \in set

TestPlus ==
    Sum(+, 1, 2) = 3

TestUnion ==
    Sum(\union, { 1 }, { 2 }) = { 1, 2 }

TestBool ==
    IsMem(FALSE, BOOLEAN)

Init == TRUE

Next == TRUE

AllTests ==
    /\ TestPlus
    /\ TestUnion
    /\ TestBool
===============================================================================
