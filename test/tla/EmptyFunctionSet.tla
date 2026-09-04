---- MODULE EmptyFunctionSet ----
\* Regression test for: https://github.com/apalache-mc/apalache/issues/3476

VARIABLES
  \* @type: Bool;
  empty,
  \* @type: Set(Int -> Int);
  fs,
  \* @type: Set(Int -> Int);
  baseline

\* @type: () => Set(Int);
Domain == IF empty THEN {} ELSE {1}

\* @type: () => Set(Int);
EmptyDomain == LET D == {} IN D

\* @type: () => Set(Int);
EmptyCodomain == LET C == {} IN C

\* @type: () => (Int -> Int);
EmptyFun == [x \in {} |-> 0]

Init ==
  /\ empty \in BOOLEAN
  /\ fs = [Domain -> EmptyCodomain]
  /\ baseline = [EmptyDomain -> EmptyCodomain]

Next == UNCHANGED <<empty, fs, baseline>>

Inv ==
  /\ baseline = [EmptyDomain -> EmptyCodomain]
  /\ fs = IF empty THEN {EmptyFun} ELSE {}
  /\ [EmptyDomain -> {1}] = {EmptyFun}
  /\ [{1} -> EmptyCodomain] = {}

====
