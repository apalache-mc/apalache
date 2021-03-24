-------------------- MODULE Fix365_ExistsSubset3 ------------------------------
(* A tricky bug that happened in evidence handling *)
EXTENDS Integers

Proc == {"p1", "p2"}
Rounds == { 0, 1, 2 }

VARIABLE
    \* @type: Set([src: Str, r: Int]);
    msgs

MT == [ src |-> STRING, r |-> Int]

As == [ src: Proc, r: Rounds]

Init ==
    /\ msgs \in SUBSET As
    \* the first ingredient of the bug
    /\ \A m \in msgs:
       m.r = 2

Next ==
    \* the second ingredient of the bug
    LET \* @type: Set(Str);
        Y == { m.src: m \in msgs } IN
    \* the third ingredient of the bug
    /\ msgs /= {}
    /\ UNCHANGED msgs

===============================================================================
