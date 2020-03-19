------------------------ MODULE NeedForTypes ------------------------------
(**
 * This simple example transforms a set into a sequence.
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS InSet     \* an input set
VARIABLES Left,     \* a storage for the yet untransformed elements
          OutSeq    \* the output sequence

ConstInit == InSet = 1..4

Init ==
    /\ OutSeq = << >>
    /\ Left = InSet

Next ==
    IF Left = {}
    THEN UNCHANGED <<Left, OutSeq>>
    ELSE \E x \in Left:
          /\ OutSeq' = Append(OutSeq, x)
          /\ Left' = Left \ {x}

Inv == InSet = Left \union { OutSeq[i]: i \in DOMAIN OutSeq }
===========================================================================
