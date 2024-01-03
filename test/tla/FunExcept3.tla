---- MODULE FunExcept3 ----

Node == { "1_OF_N", "2_OF_N", "3_OF_N" }

VARIABLE
    \* @type: N -> Set(N);
    fun1,
    \* @type: N -> Set(N);
    fun2

Init ==
    /\ fun1 = [i \in Node |-> {}]
    /\ fun2 = [i \in Node |-> {}]

Next ==
    \E i \in {"1_OF_N", "2_OF_N"} :
        /\ fun1' = [fun1 EXCEPT ![i] =  {}]
        /\ fun2' = [fun2 EXCEPT ![i] =  {}]

Sanity == fun1 = fun2

====
