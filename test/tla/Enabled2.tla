---- MODULE Enabled2 ----

EXTENDS Integers

VARIABLE
    \* @type: Int;
    x,

    \* @type: Int;
    y

Init ==
    x = 0 /\ y = 0

ActionWithPrimedVarsInNonAssignments(s, t) ==
    /\ x' = t + 1
    /\ y' = s - 1
    /\ x' > 5
    /\ x' = 6 => y' = t
    /\ x' # 6 => y' = 2

Next ==
    \/ x' = y /\ y' = x

InvActionWithPrimedVarsInNonAssignments ==
    \E s, t \in {1,2,3,4,5,6,7,8,9,10}: ENABLED ActionWithPrimedVarsInNonAssignments(s, t)


====