------------------------ MODULE UntypedConst ----------------------------------
\* typecheck should complain about a missing annotation
EXTENDS Integers

CONSTANT
    \* N is missing a type annotation
    N

VARIABLE
    \* @type: Int;
    x

Init ==
    x = N

Next ==
    x' = x + 1
===============================================================================
