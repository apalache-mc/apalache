------------------------ MODULE LocalFold2 ------------------------------------
EXTENDS Apalache, Integers, Sequences

VARIABLE 
\* @type: Int;
x

\* @type: Seq(Int);
seq == <<1,2,3>>

\* Call to FoldSeq in the doubly nested context defined by F (local r) and Q (local t)
\* @type: (Int, Int) => Int;
F(r,s) == LET \*  @type: (Int) => Int;
            Q(t) == 
            LET \* @type: (Int, Int) => Int;
                A(p,q) == p + q + r
            IN FoldSeq( A, t, seq )
          IN Q(s)

InvOfKL(k, l) == F(k, l) = F(0,0) + l + k * Len(seq)

Init == x = 0
Next == UNCHANGED x
Inv == InvOfKL(1,0)
===============================================================================
