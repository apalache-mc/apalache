---- MODULE QuantifierTest ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

Next ==
    x' = 0

ExistsTrue ==
    \E v \in {}: TRUE

ForallFalse ==
    \A v \in {}: FALSE




====