---------- MODULE Test1088 ----------

EXTENDS Integers, Apalache

\* @type: (a, a) => a;
F(x,y) ==
  \* @type: Set(a);    
  LET A == {x}
  IN IF y \in A THEN x ELSE y

Init == TRUE

Next == TRUE

Inv == F(1,1) = 1
====================
