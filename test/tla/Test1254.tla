------ MODULE Test1254 ----
EXTENDS Integers

------ MODULE base ----
\* A regression test for the bug report:
\* https://github.com/apalache-mc/apalache/issues/1254
EXTENDS Integers
VARIABLES 
    \* @type: Int;
    x
\* This is a trivial implementation of the function FF. The goal is that this function is injected from the extensionA module
\* @type: (Int) => Bool;
FF(a) == TRUE

\* @type: ( Int, (Int) => Bool ) => Bool;
Check(a, func(_)) == func(a)

Next ==
    x' = IF Check(x, FF) THEN x + 1 ELSE x

Init ==
    x = 2

GOAL == 
    x < 3
====

VARIABLES 
    \* @type: Int;
    x


\* @type: (Int) => Bool;
CheckOrig(a) ==
    a < 4

GOAL == 
    x < 5

BASE == INSTANCE base
Next ==
    x' = IF BASE!Check(x, CheckOrig) THEN x + 1 ELSE x
Init == BASE!Init
====
