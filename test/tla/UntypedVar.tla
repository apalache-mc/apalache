------------------------ MODULE UntypedVar ------------------------------------
\* typecheck should complain about a missing annotation
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* N is missing a type annotation
    x

Init ==
    x = N

Next ==
    x' = x + 1
===============================================================================
