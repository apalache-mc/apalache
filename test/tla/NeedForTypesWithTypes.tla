------------------ MODULE NeedForTypesWithTypes ---------------------------
(**
 * This simple example transforms a set into a sequence.
 *)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    InSet     \* an input set

VARIABLES
    \* @type: Set(Int);
    Left,     \* a storage for the yet untransformed elements
    \* @type: Seq(Int);
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
