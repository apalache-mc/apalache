------------------------ MODULE RangeWithConst ------------------------------------
EXTENDS Integers

VARIABLE 
\* @type: Int;
x

CONSTANT
\* @type: Int;
C

CInit == C = 1

Init == x = C
Next == UNCHANGED x
Inv == \E y \in (C + 1) .. 4 : y = 3
===============================================================================
