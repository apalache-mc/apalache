------------------------ MODULE Folds ------------------------------------
EXTENDS Integers, Apalache

VARIABLE 
\* @type: Int;
 x

Init == x = 1

Op(p,q) == p + q

Next == UNCHANGED x

Inv == FoldSet( Op, 0, {1,2,3} ) = 6 /\ FoldSeq( Op, 99, <<>> ) = 99
===============================================================================
