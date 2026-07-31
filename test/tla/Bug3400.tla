----------------- MODULE Bug3400 ---------------------
EXTENDS Integers
VARIABLE
  \* @type: Int;
  x
Init == x \in 10..200000000
Next == x' = x - 1
Inv == x >= 0

InitInv ==
    \E y \in Int:
        /\ y <= 200000000
        /\ x = y
        /\ IndInv1

IndInv1 ==
    x \in (-1000000)..200000000
================================================
