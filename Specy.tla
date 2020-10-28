------ MODULE Specy -----

EXTENDS Integers
EXTENDS Typing

(*
VARIABLES msgs

TypeAssumptions ==
  /\ AssumeType(msgs, "Set([type: Str, val: Int])")

A(x, y) == x + y

Send(m) == "[type: Str, val: Int] => Bool" :>
  msgs' = msgs \cup {m}

Init == msgs = {}

Next ==
  \E i \in 1..10:
    Send([type |-> "1a", val |-> i])
    *)

================================

