---- MODULE FunExcept2 ----

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
    /\ fun1' = [fun1 EXCEPT !["2_OF_N"] = fun1["2_OF_N"] \cup {"3_OF_N"}]
    /\ fun2' = [fun2 EXCEPT !["2_OF_N"] = fun2["2_OF_N"] \cup {"3_OF_N"}]

Sanity == fun1["1_OF_N"] = fun2["1_OF_N"]

====
