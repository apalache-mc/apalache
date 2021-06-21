------------------------ MODULE FoldSetSeq ------------------------------------
EXTENDS Apalache, Integers, Sequences

VARIABLE 
\* @type: Int;
x

\* @type: (Seq(Int), Int) => Seq(Int);
A(p,q) == Append(p,q)

Init == x = 0
Next == UNCHANGED x
Inv == FoldSet( A, <<>>, {1,2,3} ) \in {
    <<1,2,3>>, <<1,3,2>>, <<2,1,3>>, <<2,3,1>>, <<3,1,2>>,<<3,2,1>>
}
===============================================================================
