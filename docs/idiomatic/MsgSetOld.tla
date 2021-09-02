------------------------------- MODULE MsgSetOld ------------------------------

VARIABLE 
    \* @type: Set( [ type: Str, x: Int, y: Str ] );
    msgs, 
    \* @type: Bool;
    found3,
    \* @type: Bool;
    foundC


Ints == {1,2,3}
Strs == {"a","b","c"}

\* @type: () => Set([ type: Str, x: Int, y: Str ] );
Messages == [ type: {"int"}, x: Ints ] \cup [ type: {"str"}, y: Strs ]

Init == 
    /\ msgs = {}
    /\ found3 = FALSE
    /\ foundC = FALSE

Send(m) == msgs' = msgs \cup {m}
Rm(m) == msgs' = msgs \ {m}

AddIntMsg == 
    /\ \E v \in Ints: 
        /\ Send( [type |-> "int", x |-> v] )
    /\ UNCHANGED <<found3, foundC>>

CheckIntMsg == 
    /\ \E m \in msgs:
        /\ m.type = "int"
        /\ found3' = ( m.x = 3 )
        /\ Rm(m)
    /\ UNCHANGED foundC

AddStrMsg == 
    /\ \E v \in Strs: 
        /\ Send( [type |-> "str", y |-> v] )
    /\ UNCHANGED <<found3, foundC>>

CheckStrMsg == 
    /\ \E m \in msgs:
        /\ m.type = "str"
        /\ foundC' = ( m.y = "c" )
        /\ Rm(m)
    /\ UNCHANGED found3

Next ==
    \/ AddIntMsg
    \/ CheckIntMsg
    \/ AddStrMsg
    \/ CheckStrMsg

TypeOk == msgs \subseteq Messages

===============================================================================