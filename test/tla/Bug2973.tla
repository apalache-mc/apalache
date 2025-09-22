----------------------------- MODULE Bug2973 -----------------------------
\* A regression test for the case of passing the same expression to Gen.
\* Before the fix, it was producing the same constant
\* for a and b in InitSameArgs.
EXTENDS Apalache, Integers

VARIABLES 
    \* @type: Int;
    a,
    \* @type: Int;
    b

\* this should not produce a deadlock, as a and b are different constants
InitSameArgs == 
    /\ a = Gen(1)
    /\ b = Gen(1)
    /\ a /= b

\* this should not produce a deadlock, as a and b are different constants
InitDifferentArgs == 
    /\ a = Gen(1)
    /\ b = Gen(2)
    /\ a /= b

Next == UNCHANGED <<a,b>>
=============================================================================

