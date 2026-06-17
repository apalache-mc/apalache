-------------------------- MODULE NonLinearArithmetic --------------------------
EXTENDS Integers

VARIABLE
  \* @type: Int;
  x

Init == x \in 1..3

Next == x' = x

SquareNonNegative == x * x >= 0

===============================================================================
