------------------------ MODULE FoldSeqSet ------------------------------------
EXTENDS Apalache, Integers

VARIABLE 
\* @type: Int;
x

\* @type: (Set(Int), Int) => Set(Int);
A(p,q) == p \union {q}

Init == x = 0
Next == UNCHANGED x
Inv == ApaFoldSeqLeft( A, {4,4}, <<1,2,3>> ) = {1,2,3,4}
===============================================================================
