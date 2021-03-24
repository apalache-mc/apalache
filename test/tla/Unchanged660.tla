------------------------------ MODULE Unchanged660 ----------------------------
(*
 * A test for issue #660: The type checker should always treat <<x, ..., z>>
 * in UNCHANGED <<x, ..., z>> as a tuple.
 *)

VARIABLE
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init ==
    x = 1 /\ y = 2

Next ==
    /\ UNCHANGED <<x>>
    /\ UNCHANGED <<x, y>>

===============================================================================
