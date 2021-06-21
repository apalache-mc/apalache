------------------------ MODULE FoldSeqSeq ------------------------------------
EXTENDS Apalache, Integers, Sequences

VARIABLE 
\* @type: Int;
x

\* @type: (Seq(Int), Int) => Seq(Int);
A(p,q) == Append(p,q)

Init == x = 0
Next == UNCHANGED x
Inv == FoldSeq( A, <<>>, <<1,2,3>> ) = <<1,2,3>>
===============================================================================
