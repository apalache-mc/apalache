------------------------------ MODULE Rec7 ------------------------------------
EXTENDS Integers

VARIABLES f, n

(*
 Defining a recursive function without using the recursive syntax.
 Apalache v0.6.0 fails here, as CHOOSE is currently handled with a set
 comprehension. Although, in this case, it should clearly work.
 *)
Fact ==
  CHOOSE fun \in [1..5 -> Int]:
    \A k \in DOMAIN fun:
      IF k <= 1
      THEN fun[k] = 1
      ELSE fun[k] = k * fun[k - 1]

Init ==
    /\ n = 0
    /\ f = Fact[n]

Next ==     
    /\ n' = n + 1
    /\ f' = Fact[n']
===============================================================================
