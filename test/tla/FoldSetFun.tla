------------------------ MODULE FoldSetFun ------------------------------------
EXTENDS Apalache, Integers

VARIABLE 
\* @type: Int;
x

\* @type: ((Str -> Int), Str) => (Str -> Int);
A(p,q) == [p EXCEPT ![q] = 1] 
\* @type: (Str -> Int);
f == [v \in {"x","y","z"} |-> 0]

Init == x = 0
Next == UNCHANGED x
Inv == FoldSet( A, f, DOMAIN f ) = [v \in DOMAIN f |-> 1]
===============================================================================
