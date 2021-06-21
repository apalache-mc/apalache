------------------------ MODULE FoldSeqSet ------------------------------------
EXTENDS Apalache, Integers

VARIABLE 
\* @type: Int;
x

\* @type: (Set(Int), Int) => Set(Int);
A(p,q) == p \cup {q}

Init == x = 0
Next == UNCHANGED x
Inv == FoldSeq( A, {4,4}, <<1,2,3>> ) = {1,2,3,4}
===============================================================================
