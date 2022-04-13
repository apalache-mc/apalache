------------------------ MODULE LocalFold ------------------------------------
EXTENDS Apalache, Integers, Sequences

VARIABLE 
\* @type: Int;
x

\* @type: Seq(Int);
seq == <<1,2,3>>
base == 0

\* Call to ApaFoldSeqLeft in the context defined by F (local r)
F(r) == LET \* @type: (Int, Int) => Int;
            A(p,q) == p + q + r
        IN ApaFoldSeqLeft( A, base, seq )

InvOfK(k) == F(k) = F(0) + k * Len(seq)

Init == x = 0
Next == UNCHANGED x
Inv == InvOfK(1)
===============================================================================
