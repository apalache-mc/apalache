---- MODULE Lambda ----
EXTENDS Integers

A(F(_), x) == F(x)

B(y) ==
  A(LAMBDA x: x = 1, 2)
  
C(y) ==
  LET LAMBDA1(x) == x = 1 IN
  A(LAMBDA1, 2)
  
D(z) ==
  A(LAMBDA x: A(LAMBDA y: y, x), z)

(* Not supported by SANY:
E(z) ==
  (LAMBDA y: y + 1)(z)
 *)
    
(* Not supported by SANY:
F(y) ==
  A((LET LAMBDA1(x) == x = 1 IN LAMBDA1), y)
 *)
  
================================
