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

ActionWithPrimedVarsInNonAssignments ==
    /\ x' = x + 1
    /\ x' > 5
    /\ x' = 6 => FALSE

Next ==
    \/ TightlyConstrainedAction
    \/ LooselyConstrainedAction

InvLooselyConstrainedAction ==
    ENABLED LooselyConstrainedAction

InvActionWithPrimedVarsInNonAssignments ==
    ENABLED ActionWithPrimedVarsInNonAssignments

Liveness ==
    <>(ENABLED TightlyConstrainedAction)

FalseLiveness ==
    <>(~ENABLED LooselyConstrainedAction)

====