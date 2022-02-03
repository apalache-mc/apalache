---- MODULE Test1182 ----
EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
VARIABLES
    \* @typeAlias: THING = [ cnt: Int ];
    \* @type: Str -> THING;
    things

\* @type: Int => Int;
NonNegative(z) == IF 0 < z THEN z ELSE 0

\* @type: () => Bool;
Init == LET
    \* @type: () => (Str -> THING);
    F == 
        "A" :>  [
            cnt          |-> 0
        ] @@ 
        "B" :> [
            cnt          |-> 2
        ]
    \* @type: () => (Str -> THING);
    G == [
        e \in {"B", "C"} |-> 
            [
            cnt          |-> 0
            ]
        ]
    IN
    things = F @@ G

Next ==
    \/ UNCHANGED things
    \/ things' = [
           things EXCEPT !["B"] = [
               @ EXCEPT
               !.cnt = NonNegative(@ - 1)
               ]
           ]

Inv == 0 <= things["B"].cnt
====
