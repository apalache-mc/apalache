------------------------------- MODULE Specy ------------------------------- 
EXTENDS Integers, Typing

VARIABLES msgs

TypeAssumptions ==
  /\ AssumeType(msgs, "Set([type: Str, val: Int])")

A(x, y) == x + y

B == { << <<x, y>>, z >> \in <<0..10 \X 1..5, 0..4>> : x + y }

C == { <<x, y>> \in 0..10 \X 1..5 : x < y }

Send(m) == "[type: Str, val: Int] => Bool" :>
  msgs' = msgs \cup {m}

Init == msgs = {}

Next ==
  \E i \in 1..10:
    Send([type |-> "1a", val |-> i])

=============================================================================
\* Modification History
\* Last modified Mon Sep 21 18:42:57 CEST 2020 by igor
\* Created Fri Sep 18 16:26:30 CEST 2020 by igor
