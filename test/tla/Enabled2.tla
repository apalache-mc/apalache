---- MODULE Enabled2 ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x,

    \* @type: Int;
    y

Init ==
    x = 0 /\ y = 0

ActionWithPrimedVarsInNonAssignments ==
    /\ x' = x + 1 \/ x' = y + 1
    /\ x' > 5
    /\ y' \in {1, 2}
    /\ x' = 6 => y' = 1
    /\ x' # 6 => y' = 2

Next ==
    \/ x' = y /\ y' = x
    \/ ActionWithPrimedVarsInNonAssignments

InvActionWithPrimedVarsInNonAssignments ==
    ENABLED ActionWithPrimedVarsInNonAssignments


====