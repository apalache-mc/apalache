---------- MODULE Test1085 ----------

EXTENDS Integers, Apalache

\* @type: (Set(a)) => a -> Int;
PolyOper(S) == 
  LET
    \* @type: (a -> Int, a) => a -> Int;
    Add(f,e) == [ x \in DOMAIN f \union {e} |-> 0 ]
  IN FoldSet( Add, [x \in {} |-> 0], S )

Init == TRUE

Next == TRUE

Inv == PolyOper({1}) = [x \in {1} |-> 0]

====================
