---- MODULE FunctionSetEquality3477 ----
\* Regression for https://github.com/apalache-mc/apalache/issues/3477.
\* All operand emptiness combinations are explored symbolically.

VARIABLES
  \* @type: Bool;
  d1,
  \* @type: Bool;
  d2,
  \* @type: Bool;
  c1,
  \* @type: Bool;
  c2

S1 == IF d1 THEN {} ELSE {1}
S2 == IF d2 THEN {} ELSE {2}
T1 == IF c1 THEN {} ELSE {3}
T2 == IF c2 THEN {} ELSE {4}

\* @type: () => Set(Int);
Empty == {}

\* @type: () => (Int -> Int);
EmptyFun == [x \in {} |-> 0]

Init ==
  /\ d1 \in BOOLEAN
  /\ d2 \in BOOLEAN
  /\ c1 \in BOOLEAN
  /\ c2 \in BOOLEAN

Next == UNCHANGED <<d1, d2, c1, c2>>

Inv ==
  \* Disjoint nonempty domains and codomains: only the two degenerate cases can agree.
  /\ (([S1 -> T1] = [S2 -> T2]) <=>
        ((d1 /\ d2) \/ (~d1 /\ ~d2 /\ c1 /\ c2)))
  \* A shared domain does not make distinct nonempty codomains equal.
  /\ (([S1 -> T1] = [S1 -> T2]) <=> (d1 \/ (c1 /\ c2)))
  \* A shared nonempty codomain does not make distinct nonempty domains equal.
  /\ (([S1 -> {3}] = [S2 -> {3}]) <=> (d1 /\ d2))
  \* A lazy set can be equal to an ordinary empty set or the empty-function singleton.
  /\ (([S1 -> T1] = [S2 -> Empty]) <=>
        ((d1 /\ d2) \/ (~d1 /\ ~d2 /\ c1)))
  /\ (([S1 -> T1] = {EmptyFun}) <=> d1)
  /\ (([S1 -> T1] = {}) <=> (~d1 /\ c1))
  \* Nested function sets: their emptiness must also be interpreted semantically.
  /\ (([{0} -> [{1} -> T1]] = [{10} -> [{2} -> T1]]) <=> c1)

====
