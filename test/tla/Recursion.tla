----------------------------- MODULE Recursion -----------------------------
(*
 * A way to define recursive functions without having the explicit syntax
 * for recursive definitions. This is almost the same solution as in
 * [Specifying Systems, p. 67], but using the bounded CHOOSE, which allows us
 * to reconstruct the function shape.
 *
 * This example does not work in Apalache v0.6.0, as it would require Apalache
 * to expand the function set [SUBSET S -> Int].
 *
 * Igor Konnov, 2019
 *)

EXTENDS Integers

VARIABLES Set, size

a <: b == a

Card(S) ==
  LET fun ==
    CHOOSE f \in [SUBSET S -> Int]:
      \A T \in SUBSET S:
        IF T = ({} <: {Int})
        THEN f[T] = 0
        ELSE \E t \in T:
              f[T] = 1 + f[T \ {t}]
  IN
  fun[S]
      
Init ==
    /\ Set = {} <: {Int}
    /\ size = 0
    
Next ==
    \E x \in 1..10:
      /\ x \notin Set
      /\ Set' = Set \union {x}
      /\ size' = size + 1
        
Inv ==
    Card(Set) = size         

=============================================================================
\* Modification History
\* Last modified Wed Feb 05 10:45:30 CET 2020 by igor
\* Created Tue Feb 04 20:13:55 CET 2020 by igor
