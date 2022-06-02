---- MODULE Enabled ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

TightlyConstrainedAction ==
    /\ x = 1
    /\ x' = 0

LooselyConstrainedAction ==
    /\ x >= 0
    /\ x' = x + 1

Next ==
    \/ TightlyConstrainedAction
    \/ LooselyConstrainedAction

Inv ==
    ENABLED LooselyConstrainedAction

Liveness ==
    <>(ENABLED TightlyConstrainedAction)

FalseLiveness ==
    []<>(ENABLED LooselyConstrainedAction)

====