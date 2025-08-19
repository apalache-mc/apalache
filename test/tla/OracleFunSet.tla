------ MODULE OracleFunSet --------
\* A regression test for the use of sets of function sets, see:
\* https://github.com/apalache-mc/apalache/issues/1680

VARIABLES
   \* @type: Set(Bool -> Int);
  witness,
  \* @type: Bool;
  found

Init ==
  /\ witness \in {[{TRUE} -> {222521218, 0}]}
  /\ found \in BOOLEAN

Next ==
  UNCHANGED <<witness, found>>

NotFound ==
  ~found
======================