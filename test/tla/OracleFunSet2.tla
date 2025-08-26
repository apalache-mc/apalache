------ MODULE OracleFunSet2 --------
\* A regression test for function sets containing function sets, see:
\* https://github.com/apalache-mc/apalache/issues/1774

VARIABLES
   \* @type: Set((Seq(Bool) -> (Int -> Int)));
  witness,
  \* @type: Bool;
  found

Init ==
  /\ witness \in {[{<<TRUE>>} -> [{1} -> {2}]], [{<<TRUE>>} -> [{3} -> {4}]]}
  /\ found \in BOOLEAN

Next ==
  UNCHANGED <<witness, found>>

NotFound ==
  ~found
======================