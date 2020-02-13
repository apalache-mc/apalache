------------------ MODULE NeedForTypesWithTypes ---------------------------
(**
 * This simple example transforms a set into a sequence.
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS InSet     \* an input set
VARIABLES Left,     \* a storage for the yet untransformed elements
          OutSeq    \* the output sequence

a <: b == a          

ConstInit == InSet = 1..4

Init ==
    /\ OutSeq = << >> <: Seq(Int)
    /\ Left = InSet

Next ==
    IF Left = {} <: {Int}
    THEN UNCHANGED <<Left, OutSeq>>
    ELSE \E x \in Left:
          /\ OutSeq' = Append(OutSeq, x)
          /\ Left' = Left \ {x}

Inv == InSet = Left \union { OutSeq[i]: i \in DOMAIN OutSeq }
===========================================================================
