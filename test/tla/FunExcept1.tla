---- MODULE FunExcept1 ----

VARIABLE
    \* @type: Int -> Set(Int);
    fun1,
    \* @type: Int -> Set(Int);
    fun2

Init ==
    /\ fun1 = [i \in {5,6} |-> {}]
    /\ fun2 = [i \in {5,6} |-> {}]

Next ==
    /\ fun1' = [fun1 EXCEPT ![5] = fun1[5] \cup {1}]
    /\ fun2' = [fun2 EXCEPT ![5] = fun2[5] \cup {1}]

Sanity == fun1 = fun2

====
