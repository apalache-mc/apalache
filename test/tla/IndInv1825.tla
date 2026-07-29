-------------------------- MODULE IndInv1825 --------------------------
(*
 * Checking an inductive invariant. As IndInv is a conjunct of IndInit,
 * the invariant holds in the initial states by construction, see #1825.
 *)
EXTENDS Integers

VARIABLES
  \* @type: Int;
  x,
  \* @type: Int;
  y

TypeOK ==
  /\ x \in 0..10
  /\ y \in 0..10

LemmaA ==
  \A i \in 1..3: x >= 0

LemmaB ==
  y >= 5

IndInv ==
  /\ LemmaA
  /\ LemmaB

IndInit ==
  /\ TypeOK
  /\ IndInv

\* IndInit without LemmaB, so LemmaB has to be checked in state 0
PartialInit ==
  /\ TypeOK
  /\ LemmaA

Init ==
  /\ x = 0
  /\ y = 5

Next ==
  /\ x' = x + 1
  /\ y' = y - 1
=======================================================================
