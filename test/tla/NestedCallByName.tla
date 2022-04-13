---------------------- MODULE NestedCallByName -----------------------

EXTENDS Integers, Apalache

\* @type: (Int, Int) => Int;
A(x, y) == 
    LET \* @type: (Int, Int) => Int;
        F(old, new) == new
    IN ApaFoldSeqLeft(F, x, <<y>>) \* = y

Init == TRUE
Next == TRUE
Inv == ApaFoldSeqLeft(A, 0, <<1>>) = 1

=============================================================================

