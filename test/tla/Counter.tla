------ MODULE Counter ------
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    x

Init == x \in 1..1000

Next ==
    \/ x \in 1..3000 /\ x' \in x..(x + 1000)
    \/ x \in 3000..1000000 /\ x' \in x..(x + 100000)

Inv == x /= 450000

============
