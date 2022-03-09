---------------------- MODULE NestedCallByName -----------------------

EXTENDS Integers, Apalache

\* @type: (Int, Int) => Int;
A(x, y) == 
    LET \* @type: (Int, Int) => Int;
        F(old, new) == new
    IN FoldSeq(F, x, <<y>>) \* = y

Init == TRUE
Next == TRUE
Inv == FoldSeq(A, 0, <<1>>) = 1

=============================================================================

