------------------- MODULE Bug925 -----------------------
\* a regression test for the bug found in the type unifier

EXTENDS Integers, FiniteSets

\* @type: (a) => [f: Set(a)];
Optional(x) == [f |-> x]


============================================================
