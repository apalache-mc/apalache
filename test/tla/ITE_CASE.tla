------------------------------ MODULE ITE_CASE ------------------------------
VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

S == {1,2,3}

Init == /\ x \in S
        /\ y \in S

ITE(p, et, ee) ==  /\ IF p THEN et ELSE ee
                   /\ UNCHANGED y

Next == ITE( x = y', x' = 2, x' \in S )

\* @type: <<Int, Int>>;
vars == <<x, y>>

Spec == /\ Init /\ [][Next]_vars

=============================================================================
