---------- MODULE Poly1084 ----------

\* Regression test for #1084.
\* Polymorphic definitions should instantiate correctly.

EXTENDS Integers

Init == TRUE

Next == TRUE

\* @type: (a -> Int) => Set(a);
X(f) == DOMAIN f

f1 == [a \in {1} |-> 1]
fa == [a \in {"a"} |-> 1]

Inv1 ==
  /\ X(fa) = {"a"}
  /\ X(f1) = {1}

Inv2 ==
  /\ X(f1) = {1}
  /\ X(fa) = {"a"}

Inv3 == 
  LET
    A == X(fa)
  IN LET
    B == X(f1)
  IN 
  /\ A = {"a"}
  /\ B = {1}
====================
