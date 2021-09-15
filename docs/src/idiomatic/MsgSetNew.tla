------------------------------- MODULE MsgSetNew ------------------------------

VARIABLE 
    \* @type: [ int: Set([x: Int]), str: Set([y: Str]) ];
    msgs, 
    \* @type: Bool;
    found3,
    \* @type: Bool;
    foundC


Ints == {1,2,3}
Strs == {"a","b","c"}

\* no annotation required
Messages == [ 
              int |-> [x: Ints],
              str |-> [y: Strs]
            ]

Init == 
    /\ msgs = [ int |-> {}, str |-> {} ]
    /\ found3 = FALSE
    /\ foundC = FALSE

\* @type: ([x: Int]) => Bool; 
SendInt(m) == 
    msgs' = [msgs EXCEPT !.int = msgs.int \union {m}]

\* @type: ([x: Int]) => Bool; 
RmInt(m) == 
    msgs' = [msgs EXCEPT !.int = msgs.int \ {m}]

\* @type: ([y: Str]) => Bool;
SendStr(m) == 
    msgs' = [msgs EXCEPT !.str = msgs.str \union {m}]

\* @type: ([x: Int]) => Bool; 
RmStr(m) == 
    msgs' = [msgs EXCEPT !.str = msgs.str \ {m}]


AddIntMsg == 
    /\ \E v \in Ints: 
        /\ SendInt( [x |-> v] )
    /\ UNCHANGED <<found3, foundC>>

CheckIntMsg == 
    /\ \E m \in msgs.int:
        /\ found3' = ( m.x = 3 )
        /\ RmInt(m)
    /\ UNCHANGED foundC

AddStrMsg == 
    /\ \E v \in Strs: 
        /\ SendStr( [y |-> v] )
    /\ UNCHANGED <<found3, foundC>>

CheckStrMsg == 
    /\ \E m \in msgs.str:
        /\ foundC' = ( m.y = "c" )
        /\ RmStr(m)
    /\ UNCHANGED found3

Next ==
    \/ AddIntMsg
    \/ CheckIntMsg
    \/ AddStrMsg
    \/ CheckStrMsg

TypeOk == 
    /\ msgs.int \subseteq Messages.int
    /\ msgs.str \subseteq Messages.str

===============================================================================