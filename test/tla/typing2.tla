------------------------ MODULE typing2 ---------------------
\* Testing the Apalache type checker (ETC).
\* Type checking for records.

EXTENDS Typing

VARIABLE msgs

\* The assumptions about the parameters and variables.
\* The type checker cannot guess them, so we have to declare them.
LOCAL TypeAssumptions ==
  /\ AssumeType(msgs, "Set([type: Str, val: Int])")

Send(m) ==
  (msgs' = msgs \union {m})

Init ==
  msgs = {}

Next ==
  Send([type |-> "foo", val |-> 3])

==============================================================
