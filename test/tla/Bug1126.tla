------------------------------- MODULE Bug1126 --------------------------------
\* an MWE for #1126

EXTENDS Sequences

VARIABLE
    \* @type: Seq(Int);
    seq

Init ==
    seq = << >>

Next ==
    \* as apalache does not support Seq(S), it fails here
    \E s \in Seq({1, 2, 3}):
        seq' = s
===============================================================================
