------------------------ MODULE Deadlock712 ------------------------------------
(*
 This test shows that Apalache 0.15.1 can miss a deadlock.
 Discussed in issue: https://github.com/informalsystems/apalache/issues/712
 *)
EXTENDS Integers

VARIABLE
    \* @type: Int;
    x

Init ==
    x = 0

\* This transition leads to a deadlock state.
A ==
    /\ x % 2 = 0
    /\ x' = x + 1

\* An infinite sequence of B's can be applied from the initial state.
B ==
    /\ x % 2 = 0
    /\ x' = x + 2

\* An infinite sequences of Next's can be applied from the initial state.
\* Hence, Apalache does not report a deadlock.
Next ==
    A \/ B
================================================================================
