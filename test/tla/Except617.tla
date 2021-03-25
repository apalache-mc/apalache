------------------------------- MODULE Except617 ------------------------------
\* testing the advanced syntax of EXCEPT, e.g., [f EXCEPT ![r].foo = 1]
EXTENDS Integers

VARIABLE
    \* @type: Int -> [ foo: Int, bar: Str ];
    table1,
    \* @type: Str -> Str;
    table2,
    \* @type: [ num: Int, tup: <<Str, Int>> ];
    table3

Init ==
    /\ table1 = [ i \in 0..2 |-> [ foo |-> i, bar |-> "bar" ] ]
    /\ table2 = [ x \in { "a", "b" } |-> x ]
    /\ table1[1].bar = "bar"
    /\ table3 = [ num |-> 20, tup |-> <<"hello", 21>> ]

Next ==
    /\ \/ table1' = [ table1 EXCEPT ![0].foo = 3  ]
       \/ table1' = [ table1 EXCEPT ![0].foo = 3, ![1].bar = "zab" ]
       \/ table1' =
           [ table1 EXCEPT ![0].foo = 3, ![2] = [ foo |-> 1, bar |-> "baz" ] ]
    \* check that functions of strings are not always treated as records
    /\ table2' = [ table2 EXCEPT !["b"] = "c" ]
    /\ table3' = [ table3 EXCEPT !.tup[2] = 3 ]

===============================================================================
