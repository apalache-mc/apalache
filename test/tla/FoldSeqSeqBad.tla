------------------------ MODULE FoldSeqSeqBad ------------------------------------
EXTENDS Apalache, Integers, Sequences

VARIABLE 
\* @type: Int;
x

\* @type: (Seq(Int), Int) => Seq(Int);
A(p,q) == Append(p,q)

Init == x = 0
Next == UNCHANGED x
\* Asserts the negation of the invariant that should actually hold, to 
\* check if the SMT encoding is properly constrained and returns UNSAT.
Inv == FoldSeq( A, <<>>, <<1,2,3>> ) # <<1,2,3>>
===============================================================================
