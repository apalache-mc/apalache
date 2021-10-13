-------------------------------- MODULE Bug985 --------------------------------
\* This is a regression test
\* for unsound Skolemization of expressions under LET-IN:
\*
\* https://github.com/informalsystems/apalache/issues/985
VARIABLES
    \* @type: Set(Int);
    S,
    \* @type: Bool;
    tx_fail

Init ==
    /\ S = { 1, 2 }
    /\ tx_fail = TRUE

Next ==
    LET fail ==
        \* This should be true since S = { 1, 2 }.
        \* However, if we Skolemize x and then negate fail,
        \* the solver is free to use 1 as a value.
        \E x \in S:
            x /= 1
    IN
    /\ tx_fail' = fail
    /\ UNCHANGED S

\* This invariant should hold true. However, it fails in #985.
Inv ==
    tx_fail
===============================================================================
