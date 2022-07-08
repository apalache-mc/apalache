---- MODULE Bug1946 ----
VARIABLE
    \* @type: Bool;
    x

\* @type: Set(Bool -> Bool);
u == {[q \in BOOLEAN |-> TRUE]}

\* @type: Set(Bool -> Bool);
v == [BOOLEAN -> BOOLEAN]

Init == x = TRUE
Next == x' = (v /= u)
====
