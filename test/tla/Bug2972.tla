---- MODULE Bug2972 ----
\* Regression for https://github.com/apalache-mc/apalache/issues/2972
\*
\* SUBSET of an infinite set (e.g. SUBSET Int) is unsupported.  This spec
\* used to crash in LazyEquality with:
\*
\*   Unexpected equality test over types CellTFrom(Set(Int)) and InfSet[CellTFrom(Int)]
\*
\* It should now fail with a clear input error that points at the unsupported
\* SUBSET Int expression.

EXTENDS Apalache, Integers

VARIABLE
    \* @type: { p : Set({ q : Set(Int) }) };
    v

TypeOK ==
    v \in [ p: SUBSET [ q: SUBSET Int ] ]

Init ==
    /\ v = [ p |-> {[ q |-> { 1 } ]} ]
    /\ TypeOK

GenInit ==
    /\ v = Gen(1)
    /\ TypeOK

Next ==
    UNCHANGED v

====
