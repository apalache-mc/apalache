------------------------ MODULE FoldSetSeqBad ------------------------------------
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
Inv == FoldSet( A, <<>>, {1,2,3} ) \notin {
    <<1,2,3>>, <<1,3,2>>, <<2,1,3>>, <<2,3,1>>, <<3,1,2>>,<<3,2,1>>
}
===============================================================================
