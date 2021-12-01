---------- MODULE Poly1107 ----------

EXTENDS Integers, Apalache

\* @type: (a) => a -> Int;
MkFun(p) == [ x \in {p} |-> 1 ]

\* @type: (a -> Int, a -> Int) => a -> Int;
F1 (+) F2  ==
  LET 
    D1 == DOMAIN F1
    D2 == DOMAIN F2
  IN [e \in D1 \union D2 |->
      (IF e \in D1 THEN F1[e] ELSE 0)
    + (IF e \in D2 THEN F2[e] ELSE 0) ]

\* @type: (Set(a -> Int)) => a -> Int;
BigPlus(S) ==
  LET 
    NotInfix(F1,F2) == F1 (+) F2
  IN FoldSet( NotInfix, [ x \in {} |-> 1 ], S )

TestBigPlus == 
  LET 
    A1 == MkFun(1)
    A2 == MkFun(2)
  IN LET
    R ==  BigPlus({A1,A2})
  IN R = [x \in {1,2} |-> 1]

Init == TRUE

Next == TRUE

Inv == TestBigPlus

====================